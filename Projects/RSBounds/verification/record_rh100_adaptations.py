"""Record exact separated compatibility changes against the pristine RH100 snapshot."""
from pathlib import Path
import difflib
import hashlib
import json

root=Path(__file__).resolve().parent.parent
snapshot=root.parent/'sources/zeta-lab-rh100'
manifest=json.loads((snapshot/'source-manifest.json').read_text())
notes={
'HardyFirstZero.Spine':
  'Open RH100HardyZ to use the isolated upstream helper definitions and lemmas. '
  'Mathematical statements and proof logic unchanged.',
'HardyFirstZero.EulerMaclaurin':
  'Explicit public Mathlib.Analysis.PSeriesComplex import restores visibility of '
  'Complex.summable_one_div_nat_cpow. Mathematical declarations and proof bodies unchanged.',
'ZetaLean.HardyZ':
  'Isolate the existing Hardy-Z helper declarations in RH100HardyZ, avoiding the new Mathlib '
  'root hardyZ and continuous_hardyZ declarations. Qualify the Gamma-real conjugation helper. '
  'Definitions and proof logic unchanged.',
'Zeta23.FromPNTPlus.StrongPNTPrefix':
  'Explicit RemovableSingularity import restores visibility of the Cauchy derivative formula. '
  'The rational identity proof normalizes two half-differences and supplies R-r != 0 before '
  'field_simp. Mathematical declarations unchanged.',
'Zeta23.FromPNTPlus.Tactic.AdditiveCombination':
  'Mathlib removed LinearCombinationPrime. Replace its obsolete metaprogramming implementation '
  'with current kernel-proof-producing linear_combination normalized by abel. The sole downstream '
  'invocation adds eight equalities. Mathematical declarations in the closure are unchanged.',
'Zeta23.FromPNTPlus.EulerMaclaurin':
  'Explicit Mathlib.MeasureTheory.Function.Floor import restores Nat.floor measurability '
  'automation. Isolate seven generic declarations in RH100EulerMaclaurin to avoid collisions '
  'with the same PNT+ declarations independently ported by calr. Statements unchanged.',
'Zeta23.FromPNTPlus.ZetaBounds':
  'Explicit public Mathlib.Analysis.PSeriesComplex import restores visibility of '
  'Complex.summable_one_div_nat_cpow. Open the isolated RH100EulerMaclaurin namespace. '
  'Mathematical declarations and proof bodies unchanged.',
}
rows=[]
for item in manifest['files']:
    path=root/'vendor/rh100'/item['local_path']
    digest=hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != item['sha256']:
        diff=''.join(difflib.unified_diff(
            (snapshot/item['local_path']).read_text().splitlines(True),path.read_text().splitlines(True),
            fromfile='upstream/'+item['local_path'],tofile='adapted/'+item['local_path']))
        patch=root/'verification/rh100-replay'/(item['module']+'.patch')
        patch.write_text(diff)
        rows.append({'module':item['module'],'original_sha256':item['sha256'],
            'adapted_sha256':digest,'changes':notes.get(item['module'],'Pending description'),
            'diff':str(patch.relative_to(root))})
(root/'verification/rh100-adaptations.json').write_text(json.dumps({
    'repository':manifest['repository'],'commit':manifest['commit'],
    'adaptations':rows},indent=2)+'\n')
print(len(rows),'adaptations recorded')
