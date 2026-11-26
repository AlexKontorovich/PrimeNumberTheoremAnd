"""Generate kernel-checkable rational endpoint certificates from the audited brackets."""
from pathlib import Path
import json
from fractions import Fraction as Q
root=Path(__file__).resolve().parent.parent
v=json.loads((root/'verification/low-height-scalar-conditions.json').read_text())
def rat(s):
 x=Q(s);return str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'
def lc(d):return '⟨'+', '.join(str(d[k]) for k in ('k','a','b'))+'⟩'
rows=[]
for x in v['brackets']:
 for tag in ('a','b'):
  d=x['lower_endpoint' if tag=='a' else 'upper_endpoint'];n=x['index']
  rows.append(f'  ⟨{rat(x[tag])}, {lc(d["log_qlo"])}, {lc(d["log_qhi"])}, {n-1}, {n}⟩')
d=v['endpoint_100'];rows.append(f'  ⟨100, {lc(d["log_qlo"])}, {lc(d["log_qhi"])}, 28, 30⟩')
head="""import RSBounds.BacklundLowScalarBase

/-! Exact rational checks at both endpoints of the 29 certified zero brackets,
and at height 100. The checks assert no facts about zeros themselves. -/

namespace TernaryGoldbach.RSBounds.BacklundLowScalar

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificates : List MainCert := [
"""
tail="""
]

theorem certificates_length : certificates.length = 59 := by rfl

theorem certificates_checked :
    certificates.all (fun c => decide c.Valid) = true := by decide +kernel

theorem certificates_sound (c : MainCert) (hc : c ∈ certificates) :
    (c.lo : ℝ) < rosserF (c.t : ℝ) ∧ rosserF (c.t : ℝ) < (c.hi : ℝ) := by
  apply MainCert.sound
  exact of_decide_eq_true ((List.all_eq_true.mp certificates_checked) c hc)

def certificate (i : Fin 59) : MainCert :=
  certificates[i.val]'(by rw [certificates_length]; exact i.isLt)

theorem certificate_bounds (i : Fin 59) :
    ((certificate i).lo : ℝ) < rosserF ((certificate i).t : ℝ) ∧
      rosserF ((certificate i).t : ℝ) < ((certificate i).hi : ℝ) :=
  certificates_sound _ (List.getElem_mem _)

end TernaryGoldbach.RSBounds.BacklundLowScalar
"""
(root/'RSBounds/BacklundLowScalarData.lean').write_text(head+',\n'.join(rows)+tail)
print('Generated59 scalar certificates; exact checks are performed by Lean.')
