"""Check the public JSON against the exact rational Lean endpoint data.

This verifies the data transcription. The mathematical zero, multiplicity,
and completeness certificates are the separately audited Lean theorems.
"""
from pathlib import Path
from fractions import Fraction
import datetime
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
table_path = root / 'data/zeta-zeros-to-100.json'
lean_path = root / 'RSBounds/BacklundLowScalarData.lean'
table = json.loads(table_path.read_text())
endpoints = [Fraction(s.strip()) for s in re.findall(
    r'^\s*⟨([^,]+),\s*⟨', lean_path.read_text(), re.M)]
assert len(endpoints) == 59
assert table['count'] == 29 and table['height'] == [100, 1]
assert len(table['entries']) == 29
for i, row in enumerate(table['entries']):
    assert row['index'] == i + 1 and row['multiplicity'] == 1
    assert Fraction(*row['lower']) == endpoints[2 * i]
    assert Fraction(*row['upper']) == endpoints[2 * i + 1]
    assert endpoints[2 * i] < endpoints[2 * i + 1]
    if i:
        assert endpoints[2 * i - 1] < endpoints[2 * i]
record = {'kind': 'exact-data-transcription-check', 'rows': 29, 'exit_code': 0,
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in [table_path, lean_path]}}
(root / 'verification/zero-table-data.json').write_text(json.dumps(record, indent=2) + '\n')
print('All 29 rational brackets match the Lean data exactly.')
