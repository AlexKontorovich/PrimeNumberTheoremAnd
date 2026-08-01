import PrimeNumberTheoremAnd.Defs
import LeanCert.Tactic.Extension
import LeanCert.Validity.Integration
import Mathlib.Data.Rat.Floor

/-!
# LeanCert enclosures for prime-counting functions

This module is the reusable, opt-in numerical interface between PNT+ and LeanCert.
Importing it registers checked enclosures for the project definitions `pi`, `Li`, and
`Eπ`.  The candidate generators are untrusted; the associated checker theorems establish
the interval facts consumed by LeanCert.

The default `Li` enclosure uses `liPanels = 128` checked quadrature panels at each
endpoint.  Candidates wider than one are deliberately rejected so LeanCert's semantic
solver subdivides before composing the endpoint bounds into an `Eπ` enclosure.
-/

open MeasureTheory

namespace PrimeNumberTheoremAnd.CheckedEnclosures

open LeanCert.Core LeanCert.Tactic.Extension

/-! ## Exact prime-counting enclosure -/

/-- The natural-valued floor used by the exact prime-counting checker. -/
def natFloorRat (q : ℚ) : ℕ := (⌊q⌋ : ℤ).toNat

/-- Exact endpoint bounds for `pi` on a rational interval. -/
def piBounds (I : IntervalRat) : Option IntervalRat :=
  let lo := Nat.primeCounting (natFloorRat I.lo)
  let hi := Nat.primeCounting (natFloorRat I.hi)
  if h : lo ≤ hi then
    some ⟨lo, hi, by exact_mod_cast h⟩
  else none

/-- Untrusted exact candidate generator for the PNT+ definition `pi`. -/
def piCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 ≤ request.input.lo then
    match piBounds request.input with
    | some output => .ok output
    | none => .error (.inconclusive "invalid prime-counting interval")
  else .error (.domainObstruction "prime-counting enclosure requires nonnegative input")

/-- Decidable checker for a generated prime-counting enclosure. -/
def checkPi (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 ≤ request.input.lo) && decide (piBounds request.input = some output)

/-- Soundness theorem registered with LeanCert for downstream occurrences of `pi`. -/
@[leancert_enclosure piCandidate]
theorem pi_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkPi request output = true) :
    _root_.pi x ∈ output := by
  simp only [checkPi, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨hlo0, hout⟩ := hcheck
  have hfloor_lo : Nat.floor (request.input.lo : ℝ) = natFloorRat request.input.lo := by
    simp only [natFloorRat]
    rw [← Int.floor_toNat, Rat.floor_cast]
  have hfloor_hi : Nat.floor (request.input.hi : ℝ) = natFloorRat request.input.hi := by
    simp only [natFloorRat]
    rw [← Int.floor_toNat, Rat.floor_cast]
  have hpc_lo : Nat.primeCounting (natFloorRat request.input.lo) ≤
      Nat.primeCounting ⌊x⌋₊ := by
    apply Nat.monotone_primeCounting
    rw [← hfloor_lo]
    exact Nat.floor_mono hx.1
  have hpc_hi : Nat.primeCounting ⌊x⌋₊ ≤
      Nat.primeCounting (natFloorRat request.input.hi) := by
    apply Nat.monotone_primeCounting
    rw [← hfloor_hi]
    exact Nat.floor_mono hx.2
  dsimp [piBounds] at hout
  split at hout
  · simp only [Option.some.injEq] at hout
    subst output
    simp only [IntervalRat.mem_def, pi]
    constructor
    · exact_mod_cast hpc_lo
    · exact_mod_cast hpc_hi
  · simp at hout

/-! ## Checked logarithmic-integral enclosure -/

/-- Default panel count for checked `Li` endpoint quadrature. -/
def liPanels : ℕ := 128

/-- LeanCert expression for the logarithmic-integral integrand `1 / log x`. -/
def liIntegrandExpr : LeanCert.Core.Expr :=
  .inv (.log (.var 0))

/-- Checked quadrature enclosure of `Li q` for a rational endpoint `q ≥ 2`. -/
def liAt (q : ℚ) : Option IntervalRat :=
  if h : 2 ≤ q then
    LeanCert.Validity.Integration.integratePartitionChecked liIntegrandExpr
      ⟨2, q, h⟩ liPanels
  else none

/-- Endpoint-and-monotonicity enclosure of `Li` on a rational interval. -/
def liBounds (I : IntervalRat) : Option IntervalRat :=
  match liAt I.lo, liAt I.hi with
  | some lower, some upper =>
      if h : lower.lo ≤ upper.hi then some ⟨lower.lo, upper.hi, h⟩ else none
  | _, _ => none

/-- Untrusted candidate generator for `Li`, requesting subdivision above width one. -/
def liCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 2 ≤ request.input.lo then
    if request.input.hi - request.input.lo ≤ 1 then
      match liBounds request.input with
      | some output => .ok output
      | none => .error (.inconclusive "could not integrate Li endpoints")
    else .error (.inconclusive "Li enclosure requires subdivision to width at most one")
  else .error (.domainObstruction "Li enclosure requires x ≥ 2")

/-- Decidable checker for a generated logarithmic-integral enclosure. -/
def checkLi (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (2 ≤ request.input.lo) &&
    decide (request.input.hi - request.input.lo ≤ 1) &&
    decide (liBounds request.input = some output)

/-- The `Li` integrand is interval-integrable from `2` to every `b ≥ 2`. -/
theorem liIntegrable {b : ℝ} (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := by positivity
  have hlog0 : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by linarith)
  exact ContinuousAt.continuousWithinAt <|
    continuousAt_const.div (Real.continuousAt_log ht0) hlog0

/-- The PNT+ logarithmic integral is monotone on `[2, ∞)`. -/
theorem liMonoOn {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : Li a ≤ Li b := by
  unfold Li
  apply intervalIntegral.integral_mono_interval (c := 2) (d := b)
  · rfl
  · exact ha
  · exact hab
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
  · exact liIntegrable (le_trans ha hab)

/-- Soundness theorem registered with LeanCert for downstream occurrences of `Li`. -/
@[leancert_enclosure liCandidate]
theorem li_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkLi request output = true) :
    _root_.Li x ∈ output := by
  simp only [checkLi, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hlo2, _hwidth⟩, hout⟩ := hcheck
  have hhi2 : 2 ≤ request.input.hi := le_trans hlo2 request.input.le
  dsimp [liBounds] at hout
  cases hlo : liAt request.input.lo with
  | none => simp [hlo] at hout
  | some lower =>
      cases hhi : liAt request.input.hi with
      | none => simp [hlo, hhi] at hout
      | some upper =>
          simp only [hlo, hhi] at hout
          split at hout
          · simp only [Option.some.injEq] at hout
            subst output
            have hloInt : Li (request.input.lo : ℝ) ∈ lower := by
              unfold liAt at hlo
              split at hlo <;> rename_i hq
              · have hqR : (2 : ℝ) ≤ (request.input.lo : ℝ) := by exact_mod_cast hq
                have hInt : IntervalIntegrable
                    (fun x => LeanCert.Core.Expr.eval (fun _ => x) liIntegrandExpr)
                    volume (2 : ℝ) (request.input.lo : ℝ) := by
                  simpa [liIntegrandExpr] using liIntegrable hqR
                have hmem := LeanCert.Validity.Integration.integratePartitionChecked_correct
                    liIntegrandExpr ⟨2, request.input.lo, hq⟩ liPanels (by norm_num [liPanels])
                    lower hlo hInt
                simpa [Li, liIntegrandExpr] using hmem
              · exact (hq hlo2).elim
            have hhiInt : Li (request.input.hi : ℝ) ∈ upper := by
              unfold liAt at hhi
              split at hhi <;> rename_i hq
              · have hqR : (2 : ℝ) ≤ (request.input.hi : ℝ) := by exact_mod_cast hq
                have hInt : IntervalIntegrable
                    (fun x => LeanCert.Core.Expr.eval (fun _ => x) liIntegrandExpr)
                    volume (2 : ℝ) (request.input.hi : ℝ) := by
                  simpa [liIntegrandExpr] using liIntegrable hqR
                have hmem := LeanCert.Validity.Integration.integratePartitionChecked_correct
                    liIntegrandExpr ⟨2, request.input.hi, hq⟩ liPanels (by norm_num [liPanels])
                    upper hhi hInt
                simpa [Li, liIntegrandExpr] using hmem
              · exact (hq hhi2).elim
            simp only [IntervalRat.mem_def] at hloInt hhiInt ⊢
            constructor
            · exact hloInt.1.trans (liMonoOn (by exact_mod_cast hlo2) hx.1)
            · exact (liMonoOn (le_trans (by exact_mod_cast hlo2) hx.1) hx.2).trans hhiInt.2
          · simp at hout

/-! ## Composed prime-counting error enclosure -/

/-- Core expression composing input, `pi`, and `Li` enclosures into `Eπ`. -/
def epiExpr : LeanCert.Core.Expr :=
  .div (.abs (.sub (.var 1) (.var 2))) (.div (.var 0) (.log (.var 0)))

/-- Compose checked `pi` and `Li` bounds into an enclosure of `Eπ` on `I`. -/
def epiBounds (I : IntervalRat) : Option IntervalRat :=
  match piBounds I, liBounds I with
  | some piI, some liI =>
      LeanCert.Engine.evalInterval? epiExpr fun i =>
        if i = 0 then I else if i = 1 then piI else liI
  | _, _ => none

/-- Untrusted candidate generator for `Eπ`, requesting subdivision above width one. -/
def epiCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 2 ≤ request.input.lo then
    if request.input.hi - request.input.lo ≤ 1 then
      match epiBounds request.input with
      | some output => .ok output
      | none => .error (.inconclusive "could not enclose Epi on this interval")
    else .error (.inconclusive "Epi enclosure requires subdivision to width at most one")
  else .error (.domainObstruction "Epi enclosure requires x ≥ 2")

/-- Decidable checker for a composed `Eπ` enclosure. -/
def checkEpi (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (2 ≤ request.input.lo) &&
    decide (request.input.hi - request.input.lo ≤ 1) &&
    decide (epiBounds request.input = some output)

/-- Soundness theorem registered with LeanCert for downstream occurrences of `Eπ`. -/
@[leancert_enclosure epiCandidate]
theorem epi_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkEpi request output = true) :
    _root_.Eπ x ∈ output := by
  simp only [checkEpi, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hlo2, hwidth⟩, hout⟩ := hcheck
  dsimp [epiBounds] at hout
  cases hpi : piBounds request.input with
  | none => simp [hpi] at hout
  | some piI =>
      cases hli : liBounds request.input with
      | none => simp [hpi, hli] at hout
      | some liI =>
          simp only [hpi, hli] at hout
          have hpichk : checkPi request piI = true := by
            simp only [checkPi, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨le_trans (by norm_num) hlo2, hpi⟩
          have hlichk : checkLi request liI = true := by
            simp [checkLi, hlo2, hwidth, hli]
          have hpiMem : pi x ∈ piI := pi_mem hx hpichk
          have hliMem : Li x ∈ liI := li_mem hx hlichk
          have henv : LeanCert.Engine.envMem
              (fun i => if i = 0 then x else if i = 1 then pi x else Li x)
              (fun i => if i = 0 then request.input else if i = 1 then piI else liI) := by
            intro i
            by_cases hi0 : i = 0
            · simp [hi0, hx]
            · by_cases hi1 : i = 1
              · simp [hi1, hpiMem]
              · simp [hi0, hi1, hliMem]
          have hmem := LeanCert.Engine.evalInterval?_correct epiExpr
            (fun i => if i = 0 then request.input else if i = 1 then piI else liI)
            output hout
            (fun i => if i = 0 then x else if i = 1 then pi x else Li x) henv
          have hsqrt : Real.sqrt ((pi x - Li x) * (pi x - Li x)) = |pi x - Li x| := by
            rw [← pow_two, Real.sqrt_sq_eq_abs]
          simpa [epiExpr, Eπ, LeanCert.Core.Expr.abs, hsqrt] using hmem

end PrimeNumberTheoremAnd.CheckedEnclosures
