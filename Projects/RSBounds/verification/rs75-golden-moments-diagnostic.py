"""Exact rational preparation for the RS75 golden-ratio real-axis constants.

This is a diagnostic/certificate generator, not a Lean theorem. Root brackets
are checked with integer powers; logarithm brackets reproduce the existing
12-term LogCert checker. The analytic moment-to-tail reduction is recorded
in docs/RS75GoldenRatio.md and remains to be formalized.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
ROOT_SCALE = 10**12
LOG_SCALE = 10**30
N = 64

def qstr(x):
    x=Q(x)
    return f'{x.numerator}/{x.denominator}'

def add(a,b): return a[0]+b[0],a[1]+b[1]
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    c=[x*y for x in a for y in b]
    return min(c),max(c)
def scale(a,q): return mul(a,(Q(q),Q(q)))
def powi(a,j):
    out=(Q(1),Q(1))
    for _ in range(j):out=mul(out,a)
    return out

def root_floor(n,p,k):
    target=ROOT_SCALE**k
    np=n**p
    lo,hi=0,ROOT_SCALE+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k*np<=target:lo=mid
        else:hi=mid
    assert lo**k*np<=target<=(lo+1)**k*np
    return lo

def qbounds(a,b):
    lo=sum(2*LOG_SCALE*b**(2*j+1)//((2*j+1)*(2*a+b)**(2*j+1)) for j in range(12))
    hi=lo+12+3*LOG_SCALE*b**25//(25*(2*a+b)**25)+1
    return Q(lo,LOG_SCALE),Q(hi,LOG_SCALE)

def logcert(n):
    if n==1:return None,(Q(0),Q(0))
    q=Q(n);k=0
    while q>2:q/=2;k+=1
    a,b=q.denominator,q.numerator-q.denominator
    assert 0<b<=a
    c=qbounds(a,b);ln2=qbounds(1,1)
    return (k,a,b),add(scale(ln2,k),c)

logs=[logcert(n) for n in range(1,N+1)]
rows=[]
for p,k in [(233,144),(55,34)]:
    s=Q(p,k);roots=[root_floor(n,p,k) for n in range(1,N+1)]
    root_intervals=[(Q(b,ROOT_SCALE),Q(b+1,ROOT_SCALE)) for b in roots]
    # n=1 is exact, even though generic rootCheck allows the extra upper unit.
    root_intervals[0]=(Q(1),Q(1))
    L=logs[-1][1]; fN=root_intervals[-1]; a=s-1
    integral_polys=[(1/a,1/a),add(scale(L,1/a),(1/a**2,1/a**2)),
       add(add(scale(powi(L,2),1/a),scale(L,2/a**2)),(2/a**3,2/a**3))]
    moments=[]
    for j in range(3):
        partial=(Q(0),Q(0))
        for log,rt in zip(logs[:-1],root_intervals[:-1]):
            partial=add(partial,mul(powi(log[1],j),rt))
        valueN=mul(powi(L,j),fN)
        integral=scale(mul(fN,integral_polys[j]),N)
        center=add(add(partial,scale(valueN,Q(1,2))),integral)
        derivative_poly=scale(powi(L,j),s)
        if j: derivative_poly=sub(derivative_poly,scale(powi(L,j-1),j))
        assert derivative_poly[0]>0
        err=scale(mul(fN,derivative_poly),Q(1,8*N))
        interval=center[0],center[1]+err[1]
        moments.append(interval)
    rows.append({'p':p,'k':k,'roots':roots,'moments':moments})

hi,lo=rows
assert hi['moments'][0][1]<Q('2.23829')
assert hi['moments'][1][0]>Q('2.55131')
assert lo['moments'][0][0]>Q('2.2393')
assert lo['moments'][0][1]<Q('2.2394')
assert lo['moments'][1][0]>Q('2.5547')
assert lo['moments'][2][1]<Q('8.4776')
ratio_margin=Q('2.55131')/Q('2.23829')-Q('1.1398')
derivative_upper=Q('8.4776')/Q('2.2393')-(Q('2.5547')/Q('2.2394'))**2
assert ratio_margin>0 and derivative_upper<Q('2.5')
# Golden-ratio endpoint comparisons use s^2-s-1 and s>1/2.
assert Q(55,34)**2-Q(55,34)-1<0<Q(233,144)**2-Q(233,144)-1
out={'status':'exact-rational diagnostic only; analytic moment tails and Lean numeric replay pending',
     'N':N,'root_scale':ROOT_SCALE,'log_scale':LOG_SCALE,
     'log_certificates':[c for c,_ in logs],
     'point_rows':[], 'ratio_margin':qstr(ratio_margin),
     'derivative_upper':qstr(derivative_upper),'derivative_margin':qstr(Q('2.5')-derivative_upper)}
for row in rows:
    out['point_rows'].append({'p':row['p'],'k':row['k'],'root_floor_numerators':row['roots'],
        'moments':[[qstr(x) for x in interval] for interval in row['moments']],
        'moment_decimal_diagnostics':[[float(x) for x in interval] for interval in row['moments']]})
out['generator_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(ROOT/'verification/rs75-golden-moments-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'moments':[r['moment_decimal_diagnostics'] for r in out['point_rows']],
                  'ratio_margin':float(ratio_margin),'derivative_upper':float(derivative_upper)},indent=2))
