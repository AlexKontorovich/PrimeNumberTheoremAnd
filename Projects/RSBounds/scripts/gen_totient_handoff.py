"""Regenerate only the kernel-walk certificates from 71 through 557.

The trusted Lean checker is reused from SmallTotientProduct. The Python
arithmetic merely proposes certificates; `decide +kernel` checks them.
"""
from pathlib import Path

root = Path(__file__).resolve().parent.parent
base = root / "scripts/gen_small_totient_product.py"
# Reuse the exact arithmetic of the existing generator, stopping before its
# file-writing part. No existing proof source is rewritten by this execution.
env = {"__file__": str(base)}
exec(base.read_text().split("src = open(")[0], env)
state = env["states"][71]
states = {71: state}
endpoints = [171, 271, 371, 471, 557]
for n in range(71, 557):
    state = env["step"](n, state)
    if env["isP"](n + 1):
        assert env["chk"](state), n + 1
    if n + 1 in endpoints:
        states[n + 1] = state

walks = []
previous = 71
for n in endpoints:
    before, after = env["St"](states[previous]), env["St"](states[n])
    walks.append(
        f"theorem walk_{previous}_{n} : walkP {previous} {n-previous} "
        f"{before} = some {after} := by decide +kernel\n"
    )
    walks.append(
        f"theorem inv_{n} : Inv {n} {after} := "
        f"walkP_spec {n-previous} {previous} _ _ (by norm_num) "
        f"inv_{previous} walk_{previous}_{n}\n"
    )
    previous = n

target = root / "RSBounds/TotientGlobalReduction.lean"
text = target.read_text()
start = "-- BEGIN GENERATED HANDOFF WALKS\n"
end = "-- END GENERATED HANDOFF WALKS"
prefix, rest = text.split(start, 1)
_, suffix = rest.split(end, 1)
target.write_text(prefix + start + "\n".join(walks) + "\n" + end + suffix)
print("Generated five kernel walks through 557; Lean verification still required.")
