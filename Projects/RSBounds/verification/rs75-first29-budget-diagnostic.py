"""Non-certified feasibility diagnostic for the fixed RS75 b=23 quartic row.

Run from any directory. This reads the 29 checked rational brackets from
BacklundLowZeros.lean, keeps delta=0.0000211 and x=exp(23), and evaluates
the existing budget with one, eight, and sixteen disjoint cancellation
subbands. It changes no Lean source or certificate data.

Python Fraction checks are exact arithmetic, but are NOT Lean proofs.
All transcendental evaluations use mpmath and are NOT interval certificates.
The reference 57-zero head is used only to measure the cost of replacing it;
the proposed first-29 budget does not assume that reference head.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

import mpmath as mp


ROOT = Path(__file__).resolve().parent.parent
BRACKETS = ROOT / "RSBounds/BacklundLowZeros.lean"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--output", type=Path, help="Optional new JSON output file")
    args = parser.parse_args()
    assert args.digits >= 40
    mp.mp.dps = args.digits

    def real(q: Fraction) -> mp.mpf:
        return mp.mpf(q.numerator) / q.denominator

    def fmt(x: mp.mpf) -> str:
        return mp.nstr(x, min(args.digits - 10, 45))

    def rational(q: Fraction) -> str:
        return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"

    pairs = re.findall(
        r"apply value_in_bracket \(a := ([0-9 /]+)\) "
        r"\(b := ([0-9 /]+)\) \(k := ([0-9]+)\)",
        BRACKETS.read_text(),
    )
    assert [int(k) for _, _, k in pairs] == list(range(29))
    lower = [Fraction(a.replace(" ", "")) for a, _, _ in pairs]
    upper = [Fraction(b.replace(" ", "")) for _, b, _ in pairs]
    assert all(0 < l < u <= 100 for l, u in zip(lower, upper))
    assert all(upper[i] < lower[i + 1] for i in range(28))
    head_exact = sum((1 / l for l in lower), Fraction(0))
    head_bound = Fraction(592316, 1000000)
    assert head_exact < head_bound

    delta_q = Fraction(211, 10000000)
    a_q = 1 + 2 * delta_q
    r4_q = ((1 + delta_q) ** 5 + 1) ** 4
    A_q, D_q = Fraction(1894439), Fraction(100)
    L_q = 4 / (3 * delta_q)
    U_q = 2 * (1 - 4 * delta_q) / delta_q
    Y_q = 2 / delta_q
    C_q = r4_q / delta_q ** 4
    # These checks avoid evaluating the fourth root defining the crossover T.
    assert 0 < delta_q <= Fraction(22, 1000000)
    assert 4 * delta_q < 1
    assert 2 <= D_q < L_q < U_q < A_q
    assert a_q * (delta_q * U_q) ** 4 < r4_q
    assert U_q < Y_q < A_q
    assert a_q * (delta_q * Y_q) ** 4 < r4_q
    assert C_q / Y_q ** 5 - a_q / Y_q > 0
    assert r4_q < a_q * (delta_q * A_q) ** 4

    delta, a, r4 = map(real, (delta_q, a_q, r4_q))
    A, D = real(A_q), real(D_q)
    x, pi = mp.exp(23), mp.pi
    T = (r4 / a) ** mp.mpf(".25") / delta

    def F(t: mp.mpf) -> mp.mpf:
        return t / (2 * pi) * (mp.log(t / (2 * pi)) - 1) + mp.mpf(7) / 8

    def R(t: mp.mpf) -> mp.mpf:
        return (mp.mpf(".137") * mp.log(t)
                + mp.mpf(".443") * mp.log(mp.log(t)) + mp.mpf("1.588"))

    def Gprime(t: mp.mpf) -> mp.mpf:
        return (mp.log(t / (2 * pi)) / (2 * pi)
                + mp.mpf(".137") / t + mp.mpf(".443") / (t * mp.log(t)))

    def B(d: mp.mpf, n: int, s: mp.mpf) -> mp.mpf:
        return (
            s + (mp.log(T / (2 * pi)) ** 2 - mp.log(d / (2 * pi)) ** 2) / (4 * pi)
            + mp.mpf(".137") * (1 / d - 1 / T)
            + mp.mpf(".443") * (mp.e1(mp.log(d)) - mp.e1(mp.log(T)))
            + (mp.log(T / (2 * pi)) / 4 + mp.mpf(1) / 16) / (2 * pi)
            + mp.mpf(".137") / (5 * T)
            + mp.mpf(".443") * T ** 4 * mp.e1(5 * mp.log(T))
            + (F(d) + R(d) - n) / d
        )

    H = (
        (mp.log(A / (2 * pi)) / 4 + mp.mpf(1) / 16) / (2 * pi * A ** 4)
        + mp.mpf(".137") / (5 * A ** 5)
        + mp.mpf(".443") * mp.e1(5 * mp.log(A))
        + 2 * R(A) / A ** 5
    )
    b29 = B(D, 29, real(head_bound))
    b57_reference = B(mp.mpf("158.84998"), 57, mp.mpf(".8113925"))
    # Independent numerical evaluation of the integral forms. Agreement is
    # a diagnostic consistency check, never an interval enclosure.
    b_integral = (
        real(head_bound)
        + mp.quad(lambda u: Gprime(mp.exp(u)), [mp.log(D), mp.log(T)])
        + mp.quad(lambda v: Gprime(T * v) / v ** 5, [1, mp.inf])
        + (F(D) + R(D) - 29) / D
    )
    h_integral = (mp.quad(lambda v: Gprime(A * v) / v ** 5, [1, mp.inf]) / A ** 4
                  + 2 * R(A) / A ** 5)
    assert abs(b29 - b_integral) < mp.mpf(10) ** (-(args.digits - 10))
    assert abs(H - h_integral) < mp.mpf(10) ** (-(args.digits - 10))

    high_constant = r4 / delta ** 4 * H
    baseline = (2 * a * b29 / mp.sqrt(x) + (1 + 1 / x) * high_constant
                + 2 * delta + (mp.log(2 * pi) + mp.mpf(".1")) / x)
    # A second, simpler majorant: rational split Y=2/delta and elementary
    # bounds for the three 1/log(t) integrals. The resulting certificate
    # would require no E1 function and no fourth-root crossover.
    Y, C = real(Y_q), real(C_q)
    low_integral_elementary = (
        (mp.log(Y / (2 * pi)) ** 2 - mp.log(D / (2 * pi)) ** 2) / (4 * pi)
        + mp.mpf(".137") * (1 / D - 1 / Y)
        + mp.mpf(".443") * (1 / D - 1 / Y) / mp.log(D)
    )

    def fifth_power_tail_elementary(z: mp.mpf) -> mp.mpf:
        return (
            (mp.log(z / (2 * pi)) / 4 + mp.mpf(1) / 16) / (2 * pi * z ** 4)
            + mp.mpf(".137") / (5 * z ** 5)
            + mp.mpf(".443") / (5 * z ** 5 * mp.log(z))
        )

    endpoint_correction = 2 * R(Y) * (C / Y ** 5 - a / Y)
    line_elementary = (
        a * (real(head_bound) + low_integral_elementary + (F(D) + R(D) - 29) / D)
        + C * fifth_power_tail_elementary(Y) + endpoint_correction
    )
    h_elementary = fifth_power_tail_elementary(A) + 2 * R(A) / A ** 5
    high_elementary = C * h_elementary
    baseline_elementary = (
        2 * line_elementary / mp.sqrt(x) + (1 + 1 / x) * high_elementary
        + 2 * delta + (mp.log(2 * pi) + mp.mpf(".1")) / x
    )
    assert line_elementary >= a * b29 and h_elementary >= H
    target = mp.mpf(".00020211")
    sqrt_lower = mp.mpf(98715)
    assert sqrt_lower < mp.sqrt(x)
    band_results = {}
    for count in (1, 8, 16):
        cutoffs_q = [L_q + (U_q - L_q) * Fraction(j, count) for j in range(count + 1)]
        assert cutoffs_q[0] == L_q and cutoffs_q[-1] == U_q
        assert all(cutoffs_q[j] < cutoffs_q[j + 1] for j in range(count))
        cutoffs = list(map(real, cutoffs_q))
        masses = [F(cutoffs[j + 1]) - R(cutoffs[j + 1])
                  - F(cutoffs[j]) - R(cutoffs[j]) for j in range(count)]
        assert all(mass > 0 for mass in masses)
        weighted_mass = sum(masses[j] / cutoffs[j + 1] for j in range(count))
        saved_coefficient = 2 * (a - mp.mpf(".931")) * weighted_mass
        saving = saved_coefficient / mp.sqrt(x)
        q = 2 * a * b29 - saved_coefficient
        assert q > 0
        q_elementary = 2 * line_elementary - saved_coefficient
        assert q_elementary > 0
        elementary_rounded_x = (2 * delta + high_elementary + q_elementary / sqrt_lower
                               + (high_elementary + mp.log(2 * pi) + mp.mpf(".1")) / sqrt_lower ** 2)
        band_results[str(count)] = {
            "cutoffs_exact": list(map(rational, cutoffs_q)),
            "cutoffs_approx": list(map(fmt, cutoffs)),
            "count_lower_bounds": list(map(fmt, masses)),
            "weighted_count_lower_bound": fmt(weighted_mass),
            "saving": fmt(saving),
            "sqrt_coefficient_Q": fmt(q),
            "total_including_left_remainder": fmt(baseline - saving),
            "target_minus_total": fmt(target - (baseline - saving)),
            "elementary_sqrt_coefficient_Q": fmt(q_elementary),
            "elementary_total_including_left_remainder": fmt(baseline_elementary - saving),
            "elementary_target_minus_total": fmt(target - (baseline_elementary - saving)),
            "elementary_total_with_sqrt_lower_98715": fmt(elementary_rounded_x),
            "elementary_margin_with_sqrt_lower_98715": fmt(target - elementary_rounded_x),
        }

    source_paths = [
        "RSBounds/BacklundLowZeros.lean", "RSBounds/BacklundRH100Bridge.lean",
        "RSBounds/Rosser1941.lean", "RSBounds/PolynomialZeroCancellation.lean",
        "RSBounds/PolynomialRemainderBound.lean",
    ]
    output = {
        "status": "NON-CERTIFIED DIAGNOSTIC; mpmath is not interval arithmetic; no Lean theorem asserted",
        "precision_decimal_digits": args.digits,
        "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in source_paths},
        "parameters": {"A": 1894439, "D": 100, "N_D": 29,
                       "delta_exact": rational(delta_q), "m": 4, "log_x0": 23,
                       "head_bound_exact": rational(head_bound), "target": ".00020211"},
        "head": {
            "lower_brackets_exact": list(map(rational, lower)),
            "sum_reciprocal_lower_brackets_exact": rational(head_exact),
            "sum_reciprocal_lower_brackets_approx": fmt(real(head_exact)),
            "exact_python_fraction_comparison_lt_0592316": True,
        },
        "cutoff_checks": "Exact Python Fraction checks: D<L<U<T<A and kernel delta constraints; not Lean proofs",
        "crossover_T": fmt(T), "B29": fmt(b29),
        "B57_reference_only": fmt(b57_reference),
        "extra_inverse_weight_budget": fmt(b29 - b57_reference),
        "extra_relative_error_at_x0": fmt(2 * a * (b29 - b57_reference) / mp.sqrt(x)),
        "H": fmt(H), "high_tail_constant_K": fmt(high_constant),
        "baseline_including_left_remainder": fmt(baseline),
        "elementary_rational_split": {
            "Y_exact": rational(Y_q), "Y_approx": fmt(Y),
            "endpoint_coefficient_exact": rational(C_q / Y_q ** 5 - a_q / Y_q),
            "endpoint_correction": fmt(endpoint_correction),
            "line_weight": fmt(line_elementary), "H": fmt(h_elementary),
            "baseline_including_left_remainder": fmt(baseline_elementary),
            "relative_error_cost_over_E1_crossover_budget": fmt(baseline_elementary - baseline),
        },
        "independent_integral_diagnostics": {
            "B_closed_minus_quadrature": fmt(b29 - b_integral),
            "H_closed_minus_quadrature": fmt(H - h_integral),
        },
        "bands": band_results,
    }
    text = json.dumps(output, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
