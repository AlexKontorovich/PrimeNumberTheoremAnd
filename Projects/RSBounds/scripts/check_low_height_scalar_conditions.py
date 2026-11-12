"""Exact rational checks sufficient for the low-height Rosser handoff.

Uses the existing Lean q_bounds artanh enclosure (12 terms, scale10^30),
plus 3.14 < pi < 22/7. This script prepares scalar certificate conditions;
it does not assert a new Lean theorem or certify the external zero proof.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

root = Path(__file__).resolve().parent.parent
source = root.parent / "sources/zeta-lab-rh100/zero-brackets.json"
brackets = json.loads(source.read_text())["brackets"]
D = 10**30


def qbounds(a, b):
    assert 0 < b <= a
    lo = sum(2 * D * b**(2*k+1) // ((2*k+1) * (2*a+b)**(2*k+1))
             for k in range(12))
    hi = lo + 12 + 3*D*b**25 // (25*(2*a+b)**25) + 1
    return lo, hi


L2, U2 = qbounds(1, 1)


def logbounds(x):
    assert x > 1
    r, k = x, 0
    while r > 2:
        r /= 2
        k += 1
    assert 1 < r <= 2
    a, b = r.denominator, r.numerator - r.denominator
    lo, hi = qbounds(a, b)
    return {"k": k, "a": a, "b": b, "lo": k*L2+lo, "hi": k*U2+hi}


def main_bounds(t):
    qlo, qhi = t / (2*Q(22, 7)), t / (2*Q(314, 100))
    l, u = logbounds(qlo), logbounds(qhi)
    flo = qlo*Q(l["lo"], D) - qhi + Q(7, 8)
    fhi = qhi*Q(u["hi"], D) - qlo + Q(7, 8)
    return {"qlo": str(qlo), "qhi": str(qhi), "log_qlo": l, "log_qhi": u,
            "F_lower": str(flo), "F_upper": str(fhi)}, flo, fhi


records = []
for row in brackets:
    n = row["index"]
    a, b = Q(*row["a"]), Q(*row["b"])
    ra, fa, _ = main_bounds(a)
    rb, _, fb = main_bounds(b)
    assert n-1 < fa and fb < n
    records.append({"index": n, "a": str(a), "b": str(b), "lower_endpoint": ra,
                    "upper_endpoint": rb, "lower_margin": str(fa-(n-1)),
                    "upper_margin": str(n-fb)})
r100, f100lo, f100hi = main_bounds(Q(100))
assert 28 < f100lo and f100hi < 30
result = {"kind": "exact-rational-scalar-conditions-not-yet-Lean-instantiated",
          "upstream_commit": "b09fa4dd2f2182cf14b248e7ffc64ff03df2c534",
          "scale": D, "pi_lower": "157/50", "pi_upper": "22/7",
          "log_two_bounds": [L2, U2], "brackets": records,
          "endpoint_100": r100}
(root / "verification/low-height-scalar-conditions.json").write_text(json.dumps(result, indent=2)+"\n")
print("All29 exact rational endpoint conditions pass; 28 < F(100) < 30.")
print("Smallest certified lower margin:", float(min(Q(x["lower_margin"]) for x in records)))
print("Smallest certified upper margin:", float(min(Q(x["upper_margin"]) for x in records)))
