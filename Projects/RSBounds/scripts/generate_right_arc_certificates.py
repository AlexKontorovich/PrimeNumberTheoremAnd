from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import mpmath as m
m.mp.dps=100
DC=10**12
DR=10**8
U=Q(3141593,1000000)
N=16
D=64
out=['import RSBounds.BacklundRightArcNumericsBase\n','''/-! Generated rational certificates for 17 quadrature nodes.
All roots, cosine recurrences, and exponential Taylor comparisons are checked
by the Lean kernel. The generating Python calculation is not trusted. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Finset
namespace TernaryGoldbach.RSBounds.BacklundRightArc
''']
ps=[]; Bs=[]
for i in range(17):
    x=U*i/8192
    a0=(DC*(1-x*x/2)).numerator//(DC*(1-x*x/2)).denominator
    a=a0; cs=[]
    for k in range(8):
        a=(Q(2*a*a,DC)-DC).__floor__()
        cs.append(a)
    p=80 if i==16 else (64*(Q(5,4)+Q(33,25)*Q(a,DC))).__floor__()
    ps.append(p)
    bs=[]
    for j in range(1,17):
        b=int(m.floor(DR*m.mpf(j)**(-m.mpf(p)/64)))
        assert b**64*j**p<=DR**64<=(b+1)**64*j**p
        bs.append(b)
    tail=int(m.ceil(DR*m.mpf(16)**(-m.mpf(p-64)/64)))
    assert DR**64<=tail**64*16**(p-64)
    z=Q(sum(bs)+16,DR)+Q(tail,DR)/(Q(p,64)-1)
    B=int(m.ceil(m.log(m.mpf(z.numerator)/z.denominator)*10**6))+1
    Bs.append(B)
    exp=sum(Q(B,10**6)**j/factorial(j) for j in range(16))
    assert z<=exp
    out.append(f'private def roots_{i} : List ℕ := {bs}\n')
    out.append(f'''private theorem log_sample_{i} : logZeta ({p} / 64) ≤ ({B} : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := {p}) (bs := roots_{i}) (bTail := {tail})
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_{i}, Finset.sum_range_succ]
''')
    if i==16:
        out.append(f'''private theorem sigma_sample_{i} : ({p} : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * {i}) := by
  rw [show Real.pi / 32 * 16 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  norm_num
''')
    else:
        out.append(f'''private theorem sigma_sample_{i} : ({p} : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * {i}) := by
  have h := sigma_sample_lower_of_cos_cert (i := {i}) (p := {p})
    (a := {a0}) (bs := {cs})
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
''')
out.append('noncomputable def sampleP : ℕ → ℕ\n'+''.join(f'  | {i} => {p}\n' for i,p in enumerate(ps))+'  | _ => 80\n')
out.append('noncomputable def sampleB : ℕ → ℝ\n'+''.join(f'  | {i} => {B} / 1000000\n' for i,B in enumerate(Bs))+'  | _ => 0\n')
out.append('''lemma sampleP_gt_one (i : ℕ) (hi : i ≤ 16) : 1 < (sampleP i : ℝ) / 64 := by
  interval_cases i <;> norm_num [sampleP]

lemma sample_log_bound (i : ℕ) (hi : i ≤ 16) : logZeta ((sampleP i : ℝ) / 64) ≤ sampleB i := by
  interval_cases i
'''+''.join(f'  · exact log_sample_{i}\n' for i in range(17)))
out.append('''lemma sample_sigma_lower (i : ℕ) (hi : i ≤ 16) : (sampleP i : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
  interval_cases i
'''+''.join(f'  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_{i}\n' for i in range(17)))
out.append('''lemma sample_arc_bound (i : ℕ) (hi : i ≤ 16) :
    arcFunction (Real.pi / 32 * i) ≤ sampleB i := by
  have hiR : (i : ℝ) ≤ 16 := by exact_mod_cast hi
  have hmem : Real.pi / 32 * i ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hiR Real.pi_pos.le]
  exact (antitoneOn_logZeta (sampleP_gt_one i hi) (arc_sigma_gt_one hmem)
    (sample_sigma_lower i hi)).trans (sample_log_bound i hi)

/-- A certified bound stronger than the printed 0.1367 in Backlund (1918), p. 373. -/
theorem right_arc_integral_lt :
    (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi) < 0.1361 := by
  have hs : (∑ i ∈ Finset.range 16,
      (arcFunction (Real.pi / 32 * i) + arcFunction (Real.pi / 32 * ((i : ℝ) + 1))) / 2) ≤
      ∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < 16 := Finset.mem_range.mp hi
    have h0 := sample_arc_bound i (by omega)
    have h1 := sample_arc_bound (i + 1) (by omega)
    push_cast at h1
    linarith
  have hn : (∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2) / 64 < (0.1361 : ℝ) := by
    norm_num [sampleB, Finset.sum_range_succ]
  exact (right_arc_le_samples.trans (div_le_div_of_nonneg_right hs (by norm_num))).trans_lt hn

end TernaryGoldbach.RSBounds.BacklundRightArc
''')
(Path(__file__).resolve().parents[1] / 'RSBounds/BacklundRightArcNumerics.lean').write_text('\n'.join(out))
print('sampleP',ps)
print('sampleB',Bs)
print('certified trapezoid',Q(Bs[0]+Bs[-1]+2*sum(Bs[1:-1]),128*10**6))
