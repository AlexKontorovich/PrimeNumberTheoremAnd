import RSBounds.PsiFinite.Gen
/-! Benchmark files for the gate (phase D). Untrusted generator.
    lake env lean --run tools/psi_planner/GenBench.lean <outdir>
Each file holds one `checkSegK` theorem. The guard constant is 10^6/1, so that
any state passes; the kernel does the same work as with 4/5 and real states. -/
open PsiFinite PsiFinite.Gen
def cases : List (Nat × Nat) :=
  [(1058577, 4), (10495761, 5), (109586193, 5), (109061905, 7), (1000351505, 11),
   (5000144657, 12), (9999230737, 12), (9998951425, 12)]
def main (args : List String) : IO Unit := do
  let dir := args[0]!
  IO.FS.writeFile s!"{dir}/base.lean" "import RSBounds.PsiFinite.Kernel\n"
  for (lo, w) in cases do
    for sb in [16, 17, 18, 19] do
      if (sb == 19) != (lo == 9998951425) then continue
      let B := (1 <<< sb) / (1 <<< w)
      let s0 : St := ⟨0, 0, 0, 0⟩
      match runSegG 1000000 1 lo w B s0 with
      | none => IO.println s!"fail {lo} {w} {sb}"
      | some s' =>
        IO.FS.writeFile s!"{dir}/b_{lo}_{sb}.lean"
          s!"import RSBounds.PsiFinite.Kernel\n\ntheorem t : {stmt 1000000 1 lo w B s0 s'} := by\n  decide +kernel\n"
