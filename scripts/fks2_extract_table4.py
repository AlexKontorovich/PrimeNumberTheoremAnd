"""Extract Table 4 from the FKS2 extended ancillary tables.

Input: PrimeCountingTables.pdf, the ancillary document of arXiv 2206.12557
(https://arxiv.org/src/2206.12557v1/anc/PrimeCountingTables.pdf).
Output: fks2_table4_extended.json, rows [log_x1, eps_pi_num] with values
kept as strings (exponents reach e-359, beyond float64 range).

Usage: python scripts/fks2_extract_table4.py PrimeCountingTables.pdf
Requires: pypdf
"""
import json, re, sys

import pypdf

pdf_path = sys.argv[1] if len(sys.argv) > 1 else "PrimeCountingTables.pdf"
reader = pypdf.PdfReader(pdf_path)

# Table 4 spans pages 95-167 (1-indexed); rows look like
#   "3100 2.5885 e-340"  or  "12 0.0057149"
pat = re.compile(r'^(\d+(?:\.\d+)?)\s+(\d+\.\d+(?:\s*e-?\d+)?)\s*$')
rows = []
for i in range(94, len(reader.pages)):
    for line in reader.pages[i].extract_text().splitlines():
        m = pat.match(line.strip())
        if m:
            rows.append((m.group(1), m.group(2).replace(' ', '')))

# integrity: strictly increasing grid, no gaps in the 1/5/100 regimes
bs = [float(b) for b, _ in rows]
assert all(b1 > b0 for b0, b1 in zip(bs, bs[1:])), "grid not increasing"

with open("fks2_table4_extended.json", "w") as f:
    json.dump(rows, f)
print(f"extracted {len(rows)} rows: log x1 from {bs[0]:g} to {bs[-1]:g}")
