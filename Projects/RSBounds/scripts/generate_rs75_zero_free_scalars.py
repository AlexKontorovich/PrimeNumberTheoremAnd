"""Generate exact scalar certificates; correctness is checked again by Lean."""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
D=10**30; ARG_SCALE=10**12
nodes=[];cache={}
def qt(q):
 q=Q(q);return str(q.numerator) if q.denominator==1 else f'{q.numerator}/{q.denominator}'
def qb(a,b):
 lo=sum(2*D*b**(2*j+1)//((2*j+1)*(2*a+b)**(2*j+1)) for j in range(12))
 hi=lo+12+3*D*b**25//(25*(2*a+b)**25)+1
 return Q(lo,D),Q(hi,D)
def lc(q):
 q=Q(q);assert q>1;k=0
 while q>2:q/=2;k+=1
 a,b=q.denominator,q.numerator-q.denominator
 lo,hi=qb(a,b);lo2,hi2=qb(1,1)
 return (k,a,b),k*lo2+lo,k*hi2+hi
def ct(c):return '⟨'+', '.join(map(str,c))+'⟩'
def node(op,*args):
 key=(op,*args)
 if key in cache:return cache[key]
 if op=='rat':lo=hi=Q(args[0]);rhs=f'.old (.rat ({qt(lo)}))'
 elif op=='sqrt':
  q=Q(args[0]);p=10**16;n=isqrt(q.numerator*p*p//q.denominator);lo,hi=Q(n,p),Q(n+1,p)
  assert lo*lo<=q<=hi*hi
  rhs=f'.sqrtRat ({qt(q)}) ({qt(lo)}) ({qt(hi)})'
 elif op=='log':
  q=Q(args[0]);cc,lo,hi=lc(q)
  rhs=f'.old (.log {ct(cc)} {ct(cc)} (.rat ({qt(q)})))'
 elif op=='logpi':
  k=args[0];pilo=Q('3.14159265358979323846');pihi=Q('3.14159265358979323847')
  l=Q((2*pilo/k)*ARG_SCALE//1,ARG_SCALE);u=Q(-(-(2*pihi/k)*ARG_SCALE//1),ARG_SCALE)
  cl,lo,_=lc(l);cu,_,hi=lc(u)
  rhs=f'.old (.log {ct(cl)} {ct(cu)} (.mul (.mul (.rat 2) .pi) (.rat ({qt(Q(1,k))}))))'
 elif op in ['add','sub','mul']:
  a,b=[nodes[i] for i in args]
  if op=='add':lo,hi=a['lo']+b['lo'],a['hi']+b['hi']
  elif op=='sub':lo,hi=a['lo']-b['hi'],a['hi']-b['lo']
  else:
   t=[x*y for x in (a['lo'],a['hi']) for y in (b['lo'],b['hi'])];lo,hi=min(t),max(t)
  rhs=f'.{op} n{args[0]} n{args[1]}'
 elif op=='inv':
  a=nodes[args[0]];assert a['lo']>0
  lo,hi=1/a['hi'],1/a['lo'];rhs=f'.inv n{args[0]}'
 elif op=='pow':
  a,k=nodes[args[0]],args[1];lo=hi=Q(1)
  for _ in range(k):
   t=[x*y for x in (lo,hi) for y in (a['lo'],a['hi'])];lo,hi=min(t),max(t)
  rhs=f'.pow n{args[0]} {k}'
 else:raise ValueError(op)
 i=len(nodes);nodes.append(dict(lo=lo,hi=hi,rhs=rhs));cache[key]=i;return i
def rat(q):return node('rat',Q(q))
def add(a,b):return node('add',a,b)
def sub(a,b):return node('sub',a,b)
def mul(a,b):return node('mul',a,b)
def div(a,b):return mul(a,node('inv',b))
def pw(a,n):return node('pow',a,n)
q0=Q('11.1859355312082048');q1=Q('19.073344004352');qA=Q('36.506331844352')
a0,a1,A=rat(q0),rat(q1),rat(qA)
k=div(rat(1),node('sqrt',Q(5)));h=div(mul(sub(rat(1),k),A),rat(2))
s0,s1=node('sqrt',q0),node('sqrt',q1)
v=div(mul(mul(rat(2),s0),sub(s1,s0)),mul(sub(rat(1),k),A))
R1=div(mul(sub(rat(1),k),A),mul(rat(2),pw(sub(s1,s0),2)))
l=node('log',Q(17));lA=node('log',Q(1894439,17))
xA=div(v,lA)
C=sub(rat(Q('52.38865')/2),mul(a0,rat('1.1398')))
co=[]
qs=[Q(1),Q('.8'),Q('-1.04'),Q('1.2')]
for i in range(5):
 z=rat(0)
 if i==0:z=add(sub(sub(z,mul(a0,rat('.5772156646'))),rat(Q('52.38865')/2)),mul(h,l))
 if i==1:z=add(z,mul(a0,rat('.2')))
 if i<4:z=add(z,mul(mul(k,rat(qs[i])),C))
 if 1<=i<=4:z=add(z,mul(mul(mul(k,rat(qs[i-1])),a0),rat('3.3606')))
 if i<=2:z=sub(z,mul(mul(mul(div(mul(k,A),rat(2)),rat(qs[i+1])),v),rat(1)))
 if 1<=i<=3:z=sub(z,mul(mul(div(mul(k,A),rat(2)),rat(qs[i])),l))
 co.append(z)
DD=rat(0)
for j,qq in enumerate([q1,Q('11.67618784'),Q('4.7568'),Q(1)],1):DD=add(DD,mul(rat(qq),node('logpi',j)))
certs={'v':(v,Q('.339'),Q('.34')),'R1':(R1,Q('9.6459088'),Q('9.645908801')),
 'heightRatio':(xA,Q(0),Q('.029172')),'D':(DD,Q('52.38865'),None)}
for i,(idx,u) in enumerate(zip(co,map(Q,['-.26491','8.23461','27.92797','0','20.17370']))):certs['c'+str(i)]=(idx,None,u)
for name,(idx,lo,hi) in certs.items():
 assert lo is None or lo<nodes[idx]['lo'],(name,'lo')
 assert hi is None or nodes[idx]['hi']<hi,(name,'hi')
header='''import RSBounds.RS75ScalarNumericsBase
import RSBounds.RS75Parameters
import RSBounds.RS75Polynomial
import RSBounds.SmallTotientProduct

/-! Exact radical/logarithm certificates for the RS75 zero-free scalar assembly.
Generated scalar data are checked by the ordinary Lean kernel, using the existing
logarithm and interval soundness proofs. No zeta value is assumed or certified here. -/
namespace TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
open RS75ScalarNumerics
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def a0 : ℝ := 11.1859355312082048
def a1 : ℝ := 19.073344004352
def A0 : ℝ := 36.506331844352
def k0 : ℝ := 1 / Real.sqrt 5
def h : ℝ := (1 - k0) * A0 / 2
def v : ℝ := 2 * Real.sqrt a0 * (Real.sqrt a1 - Real.sqrt a0) / ((1 - k0) * A0)
def R1 : ℝ := (1 - k0) * A0 / (2 * (Real.sqrt a1 - Real.sqrt a0) ^ 2)
def heightRatio : ℝ := v / Real.log ((1894439 : ℝ) / 17)
def D : ℝ := ∑ k ∈ Finset.Icc 1 4, RS75Polynomial.coeff k * Real.log (2 * Real.pi / k)
def H : ℝ := ∑ k ∈ Finset.Icc 1 4, RS75Polynomial.coeff k / (k : ℝ) ^ 2

def c0 : ℝ := -a0 * 0.5772156646 - 52.38865 / 2 + h * Real.log 17 +
 k0 * (-a0 * 1.1398 + 52.38865 / 2) - k0 * A0 / 2 * (4 / 5) * v
def c1 : ℝ := a0 * 0.2 + k0 * (4 / 5) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * a0 * 3.3606 - k0 * A0 / 2 * (-26 / 25) * v - k0 * A0 / 2 * (4 / 5) * Real.log 17
def c2 : ℝ := k0 * (-26 / 25) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * (4 / 5) * a0 * 3.3606 - k0 * A0 / 2 * (6 / 5) * v - k0 * A0 / 2 * (-26 / 25) * Real.log 17
def c3 : ℝ := k0 * (6 / 5) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * (-26 / 25) * a0 * 3.3606 - k0 * A0 / 2 * (6 / 5) * Real.log 17
def c4 : ℝ := k0 * (6 / 5) * a0 * 3.3606
'''
lines=[header]
for i,n in enumerate(nodes):lines.append(f'private def n{i} : Expr := {n["rhs"]}')
allnames=', '.join('n'+str(i) for i in range(len(nodes)))
defs='a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4'
for name,(idx,lo,hi) in certs.items():
 lines.append(f'''\nprivate def {name}Certificate : Expr := n{idx}
private theorem {name}Certificate_checked : {name}Certificate.check = true := by decide +kernel
private theorem {name}Certificate_eval : {name}Certificate.eval = {name} := by
  norm_num [{name}Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, {allnames},
    {defs}, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring
''')
 for suffix,bound in [('lower',lo),('upper',hi)]:
  if bound is None:continue
  pred=f'({qt(bound)} : ℚ) < {name}Certificate.bounds.lo' if suffix=='lower' else f'{name}Certificate.bounds.hi < ({qt(bound)} : ℚ)'
  goal=f'({qt(bound)} : ℝ) < {name}' if suffix=='lower' else f'{name} < ({qt(bound)} : ℝ)'
  meth='Expr.lt_eval' if suffix=='lower' else 'Expr.eval_lt'
  lines.append(f'''theorem {name}_{suffix} : {goal} := by
  have hb : {pred} := by decide +kernel
  have hh := {meth} {name}Certificate_checked hb
  rw [{name}Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh
''')
lines.append('\nend\nend TernaryGoldbach.RSBounds.RS75ZeroFreeScalars\n')
path=ROOT/'RSBounds/RS75ZeroFreeNumerics.lean';path.write_text('\n'.join(lines))
record={'nodes':len(nodes),'certificates':{n:{'node':i,'lo':str(nodes[i]['lo']),'hi':str(nodes[i]['hi'])} for n,(i,l,u) in certs.items()}}
(ROOT/'verification/rs75-zero-free-scalars-generated.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'Generated {len(nodes)} nodes and {len(certs)} certificates in {path}')
