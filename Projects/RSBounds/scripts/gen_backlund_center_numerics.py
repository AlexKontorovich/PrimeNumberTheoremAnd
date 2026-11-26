"""Generate exact root bounds; Lean's kernel checks every integer inequality."""
from pathlib import Path
from math import isqrt

root = Path(__file__).resolve().parent.parent
D = 10**8
N = 625
lines = [
    "import RSBounds.BacklundCenterNumericsBase",
    "",
    "/-! Generated integer root certificates; verified with `decide +kernel`. -/",
    "set_option maxRecDepth 4096",
    "set_option maxHeartbeats 2000000",
    "",
    "namespace TernaryGoldbach.RSBounds.CenterNumerics",
    "",
]
for k in [4, 2]:
    vals = [isqrt(isqrt(D**4 // n**5)) if k == 4 else isqrt(D**2 // n**5)
            for n in range(1, N + 1)]
    name = f"roots{k}"
    lines.append(f"def {name} : List ℕ := [")
    for i in range(0, len(vals), 12):
        row = ", ".join(map(str, vals[i:i + 12]))
        lines.append("  " + row + ("," if i + 12 < len(vals) else "]"))
    lines.extend([
        "",
        f"theorem {name}_check : rootCheck 5 {k} {D} 1 {name} = true := by decide +kernel",
        f"theorem {name}_length : {name}.length = {N} := by decide +kernel",
        f"theorem {name}_sum : {name}.sum = {sum(vals)} := by decide +kernel",
        "",
        f"theorem partial5{k}_bounds :",
        f"    ({sum(vals)} : ℝ) / {D} ≤ rpowSum (5 / {k}) 1 {N} ∧",
        f"    rpowSum (5 / {k}) 1 {N} ≤ ({sum(vals) + N} : ℝ) / {D} := by",
        f"  have h := rootCheck_sound (by norm_num : 0 < 1) (by norm_num : 0 < {k})",
        f"    (by norm_num : 0 < {D}) {name}_check",
        f"  simpa only [{name}_length, {name}_sum, Nat.cast_ofNat, Nat.reduceAdd] using h",
        "",
    ])
lines.append("end TernaryGoldbach.RSBounds.CenterNumerics")
(root / "RSBounds/BacklundCenterNumericsData.lean").write_text("\n".join(lines) + "\n")
