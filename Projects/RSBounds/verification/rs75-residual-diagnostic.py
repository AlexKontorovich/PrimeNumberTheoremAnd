"""Exact-rational diagnostic for a relaxed RS75 zero-free scalar assembly.

This is not a Lean certificate or a proof oracle. The mathematical reductions
and all remaining Lean obligations are stated in docs/RS75ResidualAudit.md.
Only Python integer/Fraction arithmetic is used for decisions. Decimal strings
in the JSON are outward-rounded display bounds.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json

@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __post_init__(self):
        assert self.lo <= self.hi
    def __add__(self, b):
        b = interval(b)
        return I(self.lo+b.lo, self.hi+b.hi)
    __radd__ = __add__
    def __neg__(self): return I(-self.hi, -self.lo)
    def __sub__(self, b): return self + -interval(b)
    def __rsub__(self, b): return interval(b) + -self
    def __mul__(self, b):
        b=interval(b)
        v=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self, b):
        b=interval(b)
        assert not b.lo <= 0 <= b.hi
        return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,b): return interval(b)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        z=interval(1)
        for _ in range(n):z=z*self
        return z

def interval(a):
    if isinstance(a,I):return a
    a=Q(a)
    return I(a,a)

def sqrtq(a,digits=32):
    a=Q(a); assert a>=0
    p=10**digits
    n=isqrt(a.numerator*p*p//a.denominator)
    lo=Q(n,p);hi=Q(n+1,p)
    assert lo*lo <= a < hi*hi
    return I(lo,hi)

def log_reduced(a,n=64):
    a=Q(a); assert 1<=a<=2
    z=(a-1)/(a+1)
    s=2*sum((z**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    tail=2*z**(2*n+1)/(Q(2*n+1)*(1-z*z))
    return I(s,s+tail)

def logq(a):
    a=Q(a);assert a>0
    k=0
    while a>=2:a/=2;k+=1
    while a<1:a*=2;k-=1
    return log_reduced(a)+k*log_reduced(2)

def log_interval(a):
    a=interval(a)
    return I(logq(a.lo).lo,logq(a.hi).hi)

def display(a,digits=24):
    a=interval(a);p=10**digits
    n=a.lo.numerator*p//a.lo.denominator
    m=-((-a.hi.numerator*p)//a.hi.denominator)
    def fmt(k):
        sign='-' if k<0 else ''
        k=abs(k)
        return sign+str(k//p)+'.'+str(k%p).zfill(digits)
    return [fmt(n),fmt(m)]

a0=Q('11.1859355312082048');a1=Q('19.073344004352')
a2=Q('11.67618784');a3=Q('4.7568');a4=Q(1)
A=a1+a2+a3+a4
assert A==Q('36.506331844352')
D=Q('52.38865'); b=Q('1.1398');c=Q('3.3606');g=Q('0.5772156646')
k0=1/sqrtq(5); h=(1-k0)*A/2
v=2*sqrtq(a0)*(sqrtq(a1)-sqrtq(a0))/((1-k0)*A)
R1=(1-k0)*A/(2*(sqrtq(a1)-sqrtq(a0))**2)
l17=logq(17)
q=[Q(1),Q(4,5),-Q(26,25),Q(6,5)]
coeffs=[]
for i in range(5):
    z=interval(0)
    if i==0:z += -a0*g-D/2+h*l17
    if i==1:z += a0*Q('0.2')
    if i<len(q):z += k0*q[i]*(-a0*b+D/2)
    if 1<=i<=len(q):z += k0*q[i-1]*a0*c
    if i<=2:z -= k0*A/2*q[i+1]*v
    if 1<=i<=3:z -= k0*A/2*q[i]*l17
    coeffs.append(z)

# Simple rational upper coefficients. Drop the negative cubic term entirely.
upper=[Q('-.26491'),Q('8.23461'),Q('27.92797'),Q(0),Q('20.17370')]
assert all(ci.hi<ui for ci,ui in zip(coeffs,upper))
X=Q('.029172'); Xwide=Q('.03'); height=Q(1894439)
frequency_tail=15*Q('22.584')/height**2
assert frequency_tail<Q('1e-10')
residual_upper=sum((ui*X**i for i,ui in enumerate(upper)),Q(0))+Q('1e-10')
assert residual_upper<-Q('.0009')
assert (v/logq(height/17)).hi<X
assert R1.hi<Q('9.645908801')

# Squared kappa comparison: the remaining polynomial is positive on [0,.03].
kappa_poly_lower=125-1925*Xwide-4598*Xwide**2-197*Xwide**3-1800*Xwide**5
assert kappa_poly_lower>63
assert 1-Q(26,25)*Xwide**2>0
# The coefficient of kappa, multiplied by x, is strictly negative.
negative_coefficient_upper=a0*c*Xwide**2+D*Xwide/2-A*v.lo/2
assert negative_coefficient_upper<-Q('5.36')

# Reusable existing Mathlib pi bounds make the paper's D and H numbers enough.
pi=I(Q('3.14159265358979323846'),Q('3.14159265358979323847'))
D_actual=sum((ak*log_interval(2*pi/k) for k,ak in enumerate([a1,a2,a3,a4],1)),interval(0))
H=sum((ak/Q(k*k) for k,ak in enumerate([a1,a2,a3,a4],1)),Q(0))
assert D_actual.lo>D
assert H<Q('22.584')

# This loose golden-ratio slope follows from derivative<2.5 and sigma0-r<1.34424*x.
assert Q('2.5')*Q('1.34424')==c

out={
 'kind':'exact-rational-diagnostic-not-Lean-certificate',
 'input_gamma_lower':'0.5772156646 (proved SmallTotientProduct.gamma_bounds)',
 'unproved_analytic_inputs':['near-pole slope 0.2','golden log derivative < -1.1398',
   'golden derivative < 2.5','frequency remainder 15/t^2','Stechkin/difference assembly'],
 'constant_intervals':{'v':display(v),'R1':display(R1),'log17':display(l17),
   'v_over_log_A_over_17':display(v/logq(height/17)),
   'D_actual':display(D_actual),'H':display(H)},
 'residual_coefficient_intervals':[display(z) for z in coeffs],
 'residual_coefficient_upper':[str(z) for z in upper],
 'kappa_squared_polynomial_lower':str(kappa_poly_lower),
 'kappa_coefficient_times_x_upper':display(negative_coefficient_upper),
 'frequency_tail_upper':str(frequency_tail),
 'residual_upper_exact':str(residual_upper),
 'residual_upper_display':display(residual_upper),
 'conclusion':'All exact rational assertions passed; residual < -0.0009 on 0<x<=0.029172, conditional on stated analytic reductions.'}
path=Path(__file__).with_suffix('.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
