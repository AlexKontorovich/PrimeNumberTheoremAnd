import RSBounds.PsiFinite.Kernel

/-!
# Compiled twin of the segment checker (untrusted generator)

`runSegG` computes, with ordinary compiled code, the value that
`PsiFinite.checkSegK` should return: it counts primes per block with a byte
sieve and enumerates prime powers with loops, then applies the same
`blockStep` arithmetic as the kernel version. It is used only to *propose*
the outputs written into the generated campaign theorems; the kernel
recomputes them with `checkSegK`. Nothing proved depends on this file.

This module does not import Mathlib.
-/

namespace PsiFinite.Gen

open PsiFinite

/-- Prime counts of the `B` blocks of `2^w` odd numbers starting at `lo`. -/
def countsG (lo w B : Nat) : Array Nat := Id.run do
  let W := 1 <<< w
  let L := W * B
  let hi := lo + 2 * L - 2
  let mut comp : ByteArray := ByteArray.mk (Array.replicate L 0)
  for d in basePrimes do
    if d * d > hi then break
    let mut j := startPos lo d
    while j < L do
      comp := comp.set! j 1
      j := j + d
  let mut cs : Array Nat := Array.replicate B 0
  for k in [0:B] do
    let mut c := 0
    for i in [k * W : k * W + W] do
      if comp.get! i == 0 then c := c + 1
    cs := cs.set! k c
  return cs

/-- Proper prime powers `(m, j)`, `m = d^j`, `j ≥ 2`, `lo ≤ m ≤ top`. -/
def ppG (lo top : Nat) : List (Nat × Nat) := Id.run do
  let mut out : List (Nat × Nat) := []
  for d in 2 :: basePrimes do
    if d * d > top then break
    let mut q := d * d
    let mut j := 2
    while q ≤ top do
      if lo ≤ q then out := (q, j) :: out
      q := q * d
      j := j + 1
  return out

/-- The compiled twin of `checkSegK`. -/
def runSegG (num den lo w B : Nat) (s : St) : Option St := Id.run do
  let W := 1 <<< w
  let h := 2 * W
  let top := lo + 2 * W * B - 1
  if !(lo % 2 == 1 && 3 ≤ lo && top ≤ baseCover) then return none
  let cs := countsG lo w B
  let E := ppG lo top
  let mut st := s
  let mut A := lo - 1
  for k in [0:B] do
    let lhi' := st.lhi + logIncHi A h
    let ab := E.foldl (fun (ab : Nat × Nat) (e : Nat × Nat) =>
      if A < e.1 && e.1 ≤ A + h then (ab.1 + st.llo / e.2, ab.2 + (lhi' / e.2 + 1)) else ab) (0, 0)
    match blockStep num den A h cs[k]! ab.1 ab.2 st with
    | none => return none
    | some s' =>
      st := s'
      A := A + h
  return some st

/-- Lean source of the statement `checkSegK num den lo w B s = some s'`. -/
def stmt (num den lo w B : Nat) (s s' : St) : String :=
  s!"PsiFinite.checkSegK {num} {den} {lo} {w} {B} ⟨{s.plo}, {s.phi}, {s.llo}, {s.lhi}⟩ = " ++
  s!"some ⟨{s'.plo}, {s'.phi}, {s'.llo}, {s'.lhi}⟩"

end PsiFinite.Gen
