import RSBounds.PsiFinite.BasePrimes

/-!
# A kernel-evaluable segment checker for ψ enclosures

`checkSegK num den lo w B s` sieves the odd numbers `lo, lo+2, …, lo+2(L-1)`
with `L = 2^w * B`, counts the primes in each of the `B` blocks of `2^w` bits,
enumerates the proper prime powers of the segment, and walks the blocks
`[A, A + 2^(w+1)]`, `A = lo - 1 + 2^(w+1) k`. It keeps integer enclosures,
at scale `D = 10^30`, of `ψ(A)` and of `log A`, and checks at each block the two
directed guards of `PsiSieveBlockReduction.psi_block_abs_le_of_guards`. It
returns the enclosures at the segment's right end, or `none` if any check fails.

Everything here is meant to be *evaluated by the kernel* (`decide +kernel`).
The definitions therefore

* use the raw recursors `Nat.rec`, `List.rec`, `Bool.rec`, `Option.rec`
  (structural recursion compiles to `brecOn`, which the kernel reduces several
  times more slowly), and are `noncomputable` for that reason;
* call `Nat.add`, `Nat.land`, … directly, which the kernel evaluates with GMP;
* branch with `Bool.rec` at the call site and force each new bitset with
  `Nat.beq _ 0` before passing it on, so that accumulators stay evaluated
  literals rather than growing chains of redexes;
* wrap recursive calls in `brk`, which returns control to the kernel's
  `whnf` loop and keeps its recursion depth bounded.

Whole-segment bitsets are built with O(log) word-parallel operations per base
prime (`repK`, doubling a comb) and counted with SWAR (`swarK`); no bit is
touched individually.

This module does not import Mathlib. Its soundness is proved in
`PsiFinite.Soundness`.
-/

namespace PsiFinite

universe u

/-- The identity. Wrapping a recursive call in `brk` makes the kernel go
through a δ-step of its `whnf` loop, so evaluation does not recurse. -/
def brk {α : Sort u} (x : α) : α := x

/-- The fixed-point scale of all enclosures. -/
def D : Nat := 1000000000000000000000000000000

/-- `basePrimes` covers every odd prime `p` with `p*p ≤ baseCover`. -/
def baseCover : Nat := 10000000000

/-- Enclosures at a block end: `plo ≤ D ψ(A) ≤ phi`, `llo ≤ D log A ≤ lhi`. -/
structure St where
  plo : Nat
  phi : Nat
  llo : Nat
  lhi : Nat
deriving Repr, DecidableEq

/-! ### Non-recursive arithmetic, shared with the compiled generator -/

/-- Lower bound for `D log(1 + h/A)`: three terms of the `artanh` series in
`y = h/(2A+h)`, each rounded down. -/
def logIncLo (A h : Nat) : Nat :=
  let q := 2 * A + h
  2 * D * h / q + 2 * D * h ^ 3 / (3 * q ^ 3) + 2 * D * h ^ 5 / (5 * q ^ 5)

/-- Upper bound for `D log(1 + h/A)`: the same terms rounded up, plus a bound
for the tail `2 y^7 / (7 (1 - y^2))`. -/
def logIncHi (A h : Nat) : Nat :=
  let q := 2 * A + h
  logIncLo A h + 2 * D * h ^ 7 / (7 * q ^ 5 * (4 * A * (A + h))) + 4

/-- The integer form of `SignedEndpointSafe point D num den (up - point*D)`. -/
def guardUp (num den point up : Nat) : Bool :=
  Nat.ble up (point * D) ||
    Nat.ble ((up - point * D) * (up - point * D) * (den * den))
      (num * num * point * (D * D))

/-- The integer form of `SignedEndpointSafe point D num den (point*D - low)`. -/
def guardLow (num den point low : Nat) : Bool :=
  Nat.ble (point * D) low ||
    Nat.ble ((point * D - low) * (point * D - low) * (den * den))
      (num * num * point * (D * D))

/-- One block `[A, A+h]` with `c` primes and prime-power contributions
`ppLo ≤ D Σ Λ(p^k) ≤ ppHi`. -/
def blockStep (num den A h c ppLo ppHi : Nat) (s : St) : Option St :=
  let lhi' := s.lhi + logIncHi A h
  let plo' := s.plo + c * s.llo + ppLo
  let phi' := s.phi + c * lhi' + ppHi
  bif guardUp num den A phi' && guardLow num den (A + h) s.plo then
    some ⟨plo', phi', s.llo + logIncLo A h, lhi'⟩
  else none

/-! ### Kernel-evaluated recursion -/

/-- `repK k x s` is the OR of `x <<< (s*t)` for `t < 2^k`, when `x < 2^s`. -/
noncomputable def repK (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun _ ih x s =>
      let y := Nat.lor x (Nat.shiftLeft x s)
      brk (ih y (Nat.add s s))) k

/-- The first index `j` with `lo + 2j ≡ 0 (mod d)` and `lo + 2j ≥ d*d`, for odd
`d` and odd `lo`. -/
def startPos (lo d : Nat) : Nat :=
  bif Nat.ble lo (Nat.mul d d) then Nat.div (Nat.sub (Nat.mul d d) lo) 2
  else Nat.mod (Nat.mul (Nat.mod (Nat.sub d (Nat.mod lo d)) d) (Nat.div (Nat.add d 1) 2)) d

/-- The comb of the multiples of `d` (at least `d*d`) among the `L` bits. Bits
of index `≥ L` may also be set. -/
noncomputable def combK (lo L d : Nat) : Nat :=
  let j0 := startPos lo d
  Bool.rec 0
    (repK (Nat.succ (Nat.log2 (Nat.div (Nat.sub (Nat.sub L 1) j0) d))) (Nat.shiftLeft 1 j0) d)
    (Nat.blt j0 L)

/-- Pairs `(d^j, j)` with `d^j ≤ top`, starting from `q = d^j`, put in front of `E`. -/
noncomputable def powsUpK (fuel : Nat) :
    Nat → Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat))
    (fun _ _ _ _ E => E)
    (fun _ ih d q j top E =>
      Bool.rec E ((q, j) :: ih d (Nat.mul q d) (Nat.succ j) top E) (Nat.ble q top)) fuel

/-- Pairs `(d^j, j)` with `lo ≤ d^j ≤ top`, from `q = d^j`, put in front of `E`. -/
noncomputable def powsK (fuel : Nat) :
    Nat → Nat → Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat))
    (fun _ _ _ _ _ E => E)
    (fun _ ih d q j lo top E =>
      Bool.rec (powsUpK 64 d q j top E) (ih d (Nat.mul q d) (Nat.succ j) lo top E)
        (Nat.blt q lo)) fuel

/-- Walk the increasing list of odd base primes while `d*d ≤ hi`: OR the combs
into the composite mask and collect the prime powers `(d^j, j)`, `j ≥ 2`, in
`[lo, top]`. -/
noncomputable def sieveK (lo L hi top : Nat) (l : List Nat) :
    Nat → List (Nat × Nat) → Nat × List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat) → Nat × List (Nat × Nat))
    (fun acc E => (acc, E))
    (fun d _ ih acc E =>
      Bool.rec (acc, E)
        (let acc' := Nat.lor acc (combK lo L d)
         let E' := powsK 64 d (Nat.mul d d) 2 lo top E
         Bool.rec (brk (ih acc' E')) (brk (ih 0 E')) (Nat.beq acc' 0))
        (Nat.ble (Nat.mul d d) hi)) l

/-- `w` SWAR rounds, from fields of width `2^r`: afterwards each field of width
`2^(r+w)` holds the number of set bits of `x` in it. -/
noncomputable def swarK (L : Nat) (w : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun _ ih x r =>
      let s := Nat.shiftLeft 1 r
      let M := repK (Nat.succ (Nat.log2 (Nat.shiftRight L (Nat.succ r))))
        (Nat.sub (Nat.shiftLeft 1 s) 1) (Nat.add s s)
      let x' := Nat.add (Nat.land x M) (Nat.land (Nat.shiftRight x s) M)
      Bool.rec (brk (ih x' (Nat.succ r))) (brk (ih 0 (Nat.succ r))) (Nat.beq x' 0)) w

/-- Prime-power contributions to the block `(A, A']`: `Σ ⌊llo/j⌋` and
`Σ (⌊lhi/j⌋ + 1)` over the pairs `(m, j)` of `E` with `A < m ≤ A'`. -/
noncomputable def ppK (A A' llo lhi : Nat) (E : List (Nat × Nat)) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun a b => (a, b))
    (fun e _ ih a b =>
      Bool.rec (ih a b)
        (ih (Nat.add a (Nat.div llo e.2)) (Nat.add b (Nat.succ (Nat.div lhi e.2))))
        (Bool.and (Nat.blt A e.1) (Nat.ble e.1 A'))) E

/-- The block walk. `Y` holds the block counts in fields of width `W`; `h = 2W`. -/
noncomputable def blockLoopK (num den h W mask : Nat) (E : List (Nat × Nat)) (B : Nat) :
    Nat → Nat → St → Option St :=
  Nat.rec (motive := fun _ => Nat → Nat → St → Option St) (fun _ _ s => some s)
    (fun _ ih A Y s =>
      let pp := ppK A (Nat.add A h) s.llo (Nat.add s.lhi (logIncHi A h)) E 0 0
      Option.rec none (fun s' => brk (ih (Nat.add A h) (Nat.shiftRight Y W) s'))
        (blockStep num den A h (Nat.land Y mask) pp.1 pp.2 s)) B

/-- The segment check. `s` encloses `ψ(lo-1)` and `log(lo-1)`. -/
noncomputable def checkSegK (num den lo w B : Nat) (s : St) : Option St :=
  let W := Nat.shiftLeft 1 w
  let L := Nat.mul W B
  let top := Nat.sub (Nat.add lo (Nat.mul 2 L)) 1
  let all := Nat.sub (Nat.shiftLeft 1 L) 1
  let r := sieveK lo L (Nat.sub top 1) top basePrimes 0 (powsK 64 2 4 2 lo top [])
  let X := Nat.xor all (Nat.land r.1 all)
  Bool.rec none
    (blockLoopK num den (Nat.mul 2 W) W (Nat.sub (Nat.shiftLeft 1 W) 1) r.2 B
      (Nat.sub lo 1) (swarK L w X 0) s)
    (Bool.and (Bool.and (Nat.beq (Nat.mod lo 2) 1) (Nat.ble 3 lo)) (Nat.ble top baseCover))

end PsiFinite
