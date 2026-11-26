"""Exact-arithmetic audit of zeta(5/4)/zeta(5/2), independent of Lean.

For a decreasing positive f, the tail after N is between the integrals
from N+1 and N. Each fractional power is enclosed by exact integer-root
comparisons. The script's arithmetic uses only Python integers/Fractions;
decimal formatting is display-only. This is NOT a Lean certificate.
"""

from fractions import Fraction
from math import isqrt
from pathlib import Path
import json

N = 10000
BITS = 80
D = 1 << BITS


def inv_root_interval(n, power, root):
    """Enclose n^(-power/root) by [m/D,(m+1)/D]."""
    rhs = D ** root
    radicand = rhs // n ** power
    m = isqrt(radicand) if root == 2 else isqrt(isqrt(radicand))
    assert m ** root * n ** power <= rhs < (m + 1) ** root * n ** power
    return Fraction(m, D), Fraction(m + 1, D)


def zeta_interval(power, root):
    partial_lower = sum((inv_root_interval(n, power, root)[0]
                         for n in range(1, N + 1)), Fraction(0))
    partial_upper = partial_lower + Fraction(N, D)
    # Integral_a^infinity t^(-power/root) dt
    # = root/(power-root) * a^(-(power-root)/root).
    coefficient = Fraction(root, power - root)
    tail_lower = coefficient * inv_root_interval(N + 1, power - root, root)[0]
    tail_upper = coefficient * inv_root_interval(N, power - root, root)[1]
    return partial_lower + tail_lower, partial_upper + tail_upper


z54 = zeta_interval(5, 4)
z52 = zeta_interval(5, 2)
ratio = z54[0] / z52[1], z54[1] / z52[0]
assert Fraction(3425, 1000) < ratio[0] <= ratio[1] < Fraction(3426, 1000)
# Simple rational endpoints, rounded outwards and checked exactly.
lower = Fraction(3425382, 1000000)
upper = Fraction(3425390, 1000000)
assert lower < ratio[0] <= ratio[1] < upper


def encode(interval):
    return [{"numerator": str(x.numerator), "denominator": str(x.denominator)}
            for x in interval]


record = {
    "kind": "independent-rational-integral-test-audit-not-Lean",
    "terms": N,
    "fixed_point_bits": BITS,
    "zeta_5_over_4_interval": encode(z54),
    "zeta_5_over_2_interval": encode(z52),
    "ratio_interval": encode(ratio),
    "simplified_ratio_interval": ["3.425382", "3.425390"],
    "strictly_above_3_425": True,
    "strictly_below_3_426": True,
    "method": "positive decreasing Dirichlet series; integral-test tail; exact integer roots",
}
path = Path(__file__).with_name("backlund-center-rational.json")
path.write_text(json.dumps(record, indent=2) + "\n")
print("Exact integral-test enclosure: 3.425382 < zeta(5/4)/zeta(5/2) < 3.425390")
print("This is an independent rational audit, not a Lean proof.")
