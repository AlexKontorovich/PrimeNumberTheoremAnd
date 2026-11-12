"""Generate witness states, each independently replayed by `decide +kernel`.
Python is an untrusted producer, never a proof oracle. All calculations are
integers, with the same logarithm intervals as the proved upstream LogWalk.
"""
from pathlib import Path
from math import isqrt
import csv, hashlib, json

root=Path(__file__).resolve().parents[1]
D=10**30
LIMIT=100001
prime=bytearray(b'\1')*(LIMIT+1)
prime[0:2]=b'\0\0'
for p in range(2,isqrt(LIMIT)+1):
    if prime[p]:
        prime[p*p:LIMIT+1:p]=b'\0'*(((LIMIT-p*p)//p)+1)

def inc(n):
    q=2*n+1
    lo=sum(2*D//((2*k+1)*q**(2*k+1)) for k in range(12))
    return lo,lo+13+3*D//(25*q**25)

def fmt(s):
    return '⟨'+', '.join(map(str,s))+'⟩'

state=(0,0,0)
start=1
blocks=[]
for end in list(range(1000,100001,1000))+[LIMIT]:
    old=state
    for n in range(start,end):
        assert sum(state)<10**100, n
        lo,hi=inc(n)
        H=state[1]+hi
        if n>=2:
            assert 20*H*H<20*H*state[2]+26*D*H+10*D*D, n
        L=state[0]+lo
        state=(L,H,state[2]+(L//(n+1) if prime[n+1] else 0))
    blocks.append((start,end,old,state))
    start=end
lines=['import RSBounds.MertensFiniteWalk','', '/-!',
       '# RS62 weighted-prime lower bound for every real `1 < x ≤ 100000`',
       '', 'All 101 exact walk certificates below are checked by the Lean kernel.',
       'The generator is not in the trust base. No zero or prime asymptotic',
       'hypothesis is used, and the conclusion uses the original RS62 constant.',
       '-/', '', 'namespace TernaryGoldbach.RSBounds.MertensFiniteWalk', '',
       'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
for i,(a,b,s,t) in enumerate(blocks,1):
    lines.append(f'theorem wk_{i} : walk {a} {b-a} {fmt(s)} = some {fmt(t)} := by decide +kernel')
lines+=['',f'theorem inv_1 : Inv 1 {fmt((0,0,0))} := Inv_one']
for i,(a,b,s,t) in enumerate(blocks,1):
    lines.append(f'theorem inv_{b} : Inv {b} {fmt(t)} := walk_spec {b-a} {a} _ _ (by norm_num) inv_{a} wk_{i}')
lines+=['', '/-- The original RS62 weighted Mertens inequality, over the full real finite range. -/',
        'theorem mertens_lower_le_100000 {x : ℝ} (hx : 1 < x) (hmax : x ≤ 100000) :',
        '    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by',
        '  exact mertens_lower_of_Inv inv_100001 hx (by norm_num; linarith)', '',
        '/-- The complete RS62 statement follows from its explicit analytic tail. -/',
        'theorem mertensLower_of_tail',
        '    (htail : ∀ x : ℝ, 100000 ≤ x →',
        '      Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x) :',
        '    Goals.MertensLower := by',
        '  intro x hx',
        '  by_cases hmax : x ≤ 100000',
        '  · exact mertens_lower_le_100000 hx hmax',
        '  · exact htail x (by linarith)', '',
        'end TernaryGoldbach.RSBounds.MertensFiniteWalk','']
(root/'RSBounds/MertensFinite100000.lean').write_text('\n'.join(lines))
source=root/'RSBounds/MertensFinite100000.lean'
generator_sha=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
records=[]
for i,(a,b,s,t) in enumerate(blocks,1):
    records.append({
        'block':i, 'start_n':a, 'end_n':b, 'steps':b-a,
        'checked_integer_intervals': [max(2,a),b-1],
        'start_state':dict(zip(['Llo','Lhi','Slo'],map(str,s))),
        'end_state':dict(zip(['Llo','Lhi','Slo'],map(str,t))),
    })
data={
    'kind':'exact-fixed-point-weighted-prime-mertens-witnesses',
    'scale_D':str(D),
    'state_convention':{
        'Llo':'Llo ≤ D log n', 'Lhi':'D log n ≤ Lhi',
        'Slo':'Slo ≤ D sum_{prime p ≤ n} log(p)/p',
        'integers':'All three state fields are exact nonnegative decimal integers, encoded as strings.',
    },
    'interval_check':'20 H^2 < 20 H Slo + 26 D H + 10 D^2, H=Lhi+incrHi(n)',
    'real_conclusion':'log(x)+mertensE−1/(2 log(x)) < sum_{prime p≤x} log(p)/p, for 1<x≤100000',
    'generation_status':'All exact-integer transition and interval comparisons passed in Python. This is not a proof.',
    'kernel_replay_status':'Consult verification/mertens-finite-100000-run.json; only exit_code=0 with standard-axiom audit certifies this source.',
    'generator':'verification/gen_mertens_finite_100000.py',
    'generator_sha256':generator_sha,
    'lean_source':'RSBounds/MertensFinite100000.lean',
    'lean_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'blocks':records,
}
(root/'verification/mertens-finite-100000-witnesses.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
with (root/'verification/mertens-finite-100000-witnesses.csv').open('w',newline='') as f:
    writer=csv.writer(f)
    writer.writerow(['block','start_n','end_n','steps','D','start_Llo','start_Lhi','start_Slo','end_Llo','end_Lhi','end_Slo','generator_sha256'])
    for i,(a,b,s,t) in enumerate(blocks,1):
        writer.writerow([i,a,b,b-a,D,*s,*t,generator_sha])
print('Generated 101 exact witness blocks and matching JSON/CSV through 100001.')
