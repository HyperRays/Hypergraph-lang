"""Selected longer-cutoff and actual witness-extraction checks."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path('/Users/soham/Documents/programming/ACUIh/ACUIhE')
OUT = Path(__file__).parent
sys.path.insert(0, str(ROOT / 'Benchmarks'))
import fuzz

EXE = ROOT / '.lake/build/bin/acuihe_bench'
cases = {c['id']: c for c in json.loads((OUT / 'cases.json').read_text())}
selected = [('hom_cycle/100', 'witness'), ('hom_cycle/200', 'decision'),
            ('chain_sat/100', 'decision'), ('E_cycle/100', 'decision')]
(OUT / 'longer-metadata.json').write_text(json.dumps(dict(
    selected=selected, cutoff_s=30, repeats=1,
    executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest(),
    interpretation='Selected checks, including scaling/extraction of the observed successful family; not a full cohort rerun'), indent=2) + '\n')
with (OUT / 'longer-runs.jsonl').open('x') as stream:
    for key, mode in selected:
        result = dict(id=key, mode=mode, **fuzz.measure(EXE, cases[key], mode, 30))
        stream.write(json.dumps(result) + '\n')
        stream.flush()
        print(json.dumps(result), flush=True)
