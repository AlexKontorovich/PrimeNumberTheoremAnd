"""Generate the FKS2 extended Table 4 cell shards (towards PNT#721).

Input: fks2_table4_extended.json, produced by scripts/fks2_extract_table4.py
from the FKS2 ancillary tables (arXiv 2206.12557).
Output: PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4ExtData_*.lean —
shard files with `List Cell` literals and one `native_decide` check lemma
each (see Table4ExtCore.lean for the Cell semantics).

Cell = (b, b', eps, slo, shi):
  b, b'      consecutive integer grid points
  eps        table value eps_pi_num(e^b), exact rational
  slo, shi   outward rational sqrt enclosures: slo^2 <= b, b' <= shi^2

Usage: python scripts/fks2_gen_table4_cells.py [fks2_table4_extended.json]
"""
import json, math, os, sys
from fractions import Fraction

SRC = sys.argv[1] if len(sys.argv) > 1 else "fks2_table4_extended.json"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                   "PrimeNumberTheoremAnd", "IEANTN", "FKS2Tables")
BMAX = 20000
SHARD = 1000
DEN = 10**5

def to_frac(s: str) -> Fraction:
    if 'e' in s:
        m, e = s.split('e')
        return Fraction(m) * Fraction(10) ** int(e)
    return Fraction(s)

def sqrt_lo(n: int) -> Fraction:
    v = Fraction(math.floor(math.sqrt(n) * DEN), DEN)
    while v * v > n:
        v -= Fraction(1, DEN)
    assert v * v <= n
    return v

def sqrt_hi(n: int) -> Fraction:
    v = Fraction(math.ceil(math.sqrt(n) * DEN), DEN)
    while v * v < n:
        v += Fraction(1, DEN)
    assert v * v >= n
    return v

def q(fr: Fraction) -> str:
    return f"{fr.numerator}/{fr.denominator}" if fr.denominator != 1 else str(fr.numerator)

rows = [(int(b), to_frac(v)) for b, v in json.load(open(SRC))
        if float(b) <= BMAX]
rows.sort()
cells = [(b0, b1, e0, sqrt_lo(b0), sqrt_hi(b1))
         for (b0, e0), (b1, _) in zip(rows, rows[1:])]
print(f"{len(rows)} rows -> {len(cells)} cells (b <= {BMAX})")

for i in range(0, len(cells), SHARD):
    chunk = cells[i:i+SHARD]
    idx = i // SHARD
    name = f"Table4ExtData_{idx:02d}"
    lines = [
        "import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtCore",
        "",
        f"/-! Generated shard {idx}: cells [{chunk[0][0]}, {chunk[-1][1]}] of the",
        "extended ancillary Table 4 (see Table4ExtCore for provenance).",
        "Regenerate with scripts/fks2_gen_table4_cells.py. -/",
        "",
        "namespace FKS2.Table4Ext",
        "",
        "set_option maxRecDepth 100000",
        "set_option linter.style.nativeDecide false",
        "",
        f"def cells_{idx:02d} : List Cell := [",
        ",\n".join(f"  ⟨{b0}, {b1}, {q(e)}, {q(lo)}, {q(hi)}⟩"
                   for b0, b1, e, lo, hi in chunk),
        "]",
        "",
        f"theorem cells_{idx:02d}_checked :",
        f"    cells_{idx:02d}.all checkCell = true := by native_decide",
        "",
        "end FKS2.Table4Ext",
        "",
    ]
    with open(os.path.join(OUT, name + ".lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
print("done")
