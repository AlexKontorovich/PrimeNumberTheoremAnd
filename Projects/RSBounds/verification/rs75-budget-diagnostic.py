"""Numerical diagnostics, not a Lean theorem or interval certificate.

Inputs were supplied during the RS75/S76 source audit. This script assumes the
stated head sums and two-sided zero-count envelope; it does not verify them.
The head S(D) means sum_{0<Im(rho)<=D} 1/abs(rho), with multiplicity.
Only the tail strictly above D is majorized using 1/Im(rho).
It evaluates an intentionally crude fourfold smoothing budget without a
zero-free region, then evaluates the numerical effect of cancellation in one integration.
The companion Lean modules prove the common-band kernel estimate; this script
does not certify the zero-count inputs, summation assembly, or total budget.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
M = mp.mpf
A = M(1894439)
x = mp.exp(23)
pi = mp.pi

def F(t):
    return t / (2 * pi) * (mp.log(t / (2 * pi)) - 1) + M(7) / 8

def R(t):
    return M('.137') * mp.log(t) + M('.443') * mp.log(mp.log(t)) + M('1.588')

H = ((mp.log(A / (2 * pi)) / 4 + M(1) / 16) / (2 * pi * A**4)
     + M('.137') / (5 * A**5) + M('.443') * mp.e1(5 * mp.log(A))
     + 2 * R(A) / A**5)

def budget(delta, D, N, S):
    a = 1 + 2 * delta
    R4 = ((1 + delta)**5 + 1)**4
    T = (R4 / a)**M('.25') / delta
    B = (S + (mp.log(T / (2 * pi))**2 - mp.log(D / (2 * pi))**2) / (4 * pi)
         + M('.137') * (1 / D - 1 / T)
         + M('.443') * (mp.e1(mp.log(D)) - mp.e1(mp.log(T)))
         + (mp.log(T / (2 * pi)) / 4 + M(1) / 16) / (2 * pi)
         + M('.137') / (5 * T) + M('.443') * T**4 * mp.e1(5 * mp.log(T))
         + (F(D) + R(D) - N) / D)
    line = 2 * a * B / mp.sqrt(x)
    high = R4 / delta**4 * (1 + 1 / x) * H
    main = 2 * delta + mp.log(2 * pi) / x
    return dict(delta=delta, crossover=T, B=B, line=line, high=high,
                main=main, total=line + high + main)

heads = [('RS75', M('158.84998'), 57, M('.8113925')),
         ('S76', M('12030.00896'), 12555, M('4.52756275'))]
results = {}
for label, D, N, S in heads:
    opt = mp.findroot(lambda d: mp.diff(lambda dd: budget(dd, D, N, S)['total'], d),
                      (M('.000020'), M('.000023')))
    results[label] = {'fixed': budget(M('.0000211'), D, N, S),
                      'optimized': budget(opt, D, N, S)}

# One-integration cancellation, on a band wholly below the low/high crossover.
# The proposed bound is |kernel| <= .914/gamma on [1.85/delta, 2*(1-4*delta)/delta].
delta = results['S76']['optimized']['delta']
L, U = M('1.85') / delta, 2 * (1 - 4 * delta) / delta
count_lower = F(U) - R(U) - F(L) - R(L)
saving = 2 * (1 + 2 * delta - M('.914')) * count_lower / (U * mp.sqrt(x))
numerator_bound = (M('1.5') * mp.sqrt(1 + 4 * delta) * delta
                   + 2 * (1 + 3 * delta)**M('1.5') * (M(5) / 6 + M(1) / 100))
results['proposed_cancellation_improvement'] = dict(
    lower=L, upper=U, count_lower=count_lower,
    first_antiderivative_numerator_bound=numerator_bound,
    proposed_uniform_kernel_coefficient=M('.914'),
    saving=saving,
    improved_total=results['S76']['optimized']['total'] - saving,
    target=M('.00020211'))


# Sharper cubic sine bound: sin(theta) <= theta - (47/300) theta**3,
# for 0 <= theta <= 1, follows from Mathlib's Real.sin_bound.
# This predicts |kernel| <= .931/gamma on [4/(3*delta), 2*(1-4*delta)/delta],
# using only the small RS75 head. PolynomialZeroCancellation proves the
# common-band kernel lemma. The count certificates and total budget remain
# uncertified by this diagnostic script.
worst_delta = M('.000022')
coefficient_upper = (M(3) / 2 * worst_delta
    + (1 + 3 * worst_delta)**2 / (1 - 4 * worst_delta)
    - M(47) / 675 / (1 + 4 * worst_delta)**3)
results['proposed_cubic_sine_band'] = {'coefficient_upper': coefficient_upper}
for label in ['fixed', 'optimized']:
    delta = results['RS75'][label]['delta']
    L, U = 4 / (3 * delta), 2 * (1 - 4 * delta) / delta
    count_lower = F(U) - R(U) - F(L) - R(L)
    saving = 2 * (1 + 2 * delta - M('.931')) * count_lower / (U * mp.sqrt(x))
    results['proposed_cubic_sine_band'][label] = dict(
        delta=delta, lower=L, upper=U, count_lower=count_lower,
        saving=saving, improved_total=results['RS75'][label]['total'] - saving)

def stringify(obj):
    if isinstance(obj, dict):
        return {k: stringify(v) for k, v in obj.items()}
    return mp.nstr(obj, 45)

output = {'status': 'UNPROVED NUMERICAL DIAGNOSTIC; not interval arithmetic',
          'precision_decimal_digits': mp.mp.dps,
          'band_convention': 'Both signs: upper endpoint 2*(1-4*delta)/delta',
          'results': stringify(results)}
path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
