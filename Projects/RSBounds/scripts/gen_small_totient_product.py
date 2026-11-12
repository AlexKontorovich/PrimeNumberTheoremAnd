"""Generates RSBounds/SmallTotientProduct.lean for primes 5 <= x <= 71. Adapted from the pinned calr3/ternary-goldbach generator."""
import os
from fractions import Fraction as Fr
import math
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
D = 10**30; K = 12; TOP = 71
def incrLo(n): return sum(2*D//((2*k+1)*(2*n+1)**(2*k+1)) for k in range(K))
def incrHi(n): return incrLo(n)+K+3*D//(25*(2*n+1)**25)+1
def isP(p):
    if p < 2: return False
    d = 2
    while d*d <= p:
        if p % d == 0: return False
        d += 1
    return True
def qAux(a, b): return sum(2*D*b**(2*k+1)//((2*k+1)*(2*a+b)**(2*k+1)) for k in range(K))
def qLo(a, b): return qAux(a, b)
def qHi(a, b): return qAux(a, b) + K + 3*D*b**25//(25*(2*a+b)**25) + 1
def cdiv(x, y): return (x + y - 1)//y
# G <= D e^gamma: Taylor sum at 0.5772156646, 22 terms
g = Fr(5772156646, 10**10)
S = sum(g**i / math.factorial(i) for i in range(22))
Glo = (D * S.numerator) // S.denominator - 1
def adv(f, T, m, lo, hi):
    while f > 0 and D*(m+1) <= T:
        lo += incrLo(m); hi += incrHi(m); m += 1; f -= 1
    return m, lo, hi
def chk(s):
    Llo, Lhi, Tlo, Thi, Fhi, m, Mlo, Mhi = s
    a = D*m
    if not (a < Tlo and Thi - a <= a): return False
    A = Mlo + qLo(a, Tlo - a); B = Mhi + qHi(a, Thi - a)
    return Fhi < Glo*A//D + 250637*10**55//B
def step(n, s):
    Llo, Lhi, Tlo, Thi, Fhi, m, Mlo, Mhi = s
    Llo += incrLo(n); Lhi += incrHi(n)
    if isP(n+1):
        Tlo += Llo; Thi += Lhi
        m, Mlo, Mhi = adv(30, Tlo, m, Mlo, Mhi)
        Fhi = cdiv(Fhi*(n+1), n)
    return (Llo, Lhi, Tlo, Thi, Fhi, m, Mlo, Mhi)
s = (0, 0, 0, 0, D, 1, 0, 0)
bounds = [1, TOP]
states = {1: s}; n = 1
worst = None
for b in bounds[1:]:
    while n < b:
        s = step(n, s)
        if isP(n+1) and n+1 >= 5:
            assert chk(s), n+1
        n += 1
    states[n] = s
def St(v): return "⟨" + ", ".join(str(x) for x in v) + "⟩"
walks = ""
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem wk_{i} : walkP {a} {b-a} {St(states[a])} = some {St(states[b])} := by decide +kernel\n"
walks += f"\ntheorem inv_1 : Inv 1 {St(states[1])} := Inv_one\n"
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem inv_{b} : Inv {b} {St(states[b])} := walkP_spec {b-a} {a} _ _ (by norm_num) inv_{a} wk_{i}\n"
src = open(os.path.join(HERE, "SmallMertensProd.tmpl")).read()
src = src.replace("@WALKS@", walks).replace("@GLO@", str(Glo)).replace("@TOP@", str(TOP))
open(os.path.join(ROOT, "RSBounds/SmallTotientProduct.lean"), "w").write(src)
print("Glo", Glo, "chunks", len(bounds)-1)
