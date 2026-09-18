"""Small deterministic scaling probe, not a random-workload performance claim."""
import collections
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

ROOT = Path('/Users/soham/Documents/programming/ACUIh/ACUIhE')
sys.path.insert(0, str(ROOT / 'Benchmarks'))
import fuzz

OUT = Path(__file__).parent
EXE = ROOT / '.lake/build/bin/acuihe_bench'
LIMIT = 5.0
REPEATS = 3

def make_case(kind, n):
    def v(i): return ('v', i)
    a = ('c', 0)
    if kind.startswith('chain_'):
        nv = n - 1
        pairs = [(v(i), v(i + 1)) for i in range(nv - 1)]
        pairs += [(v(0), a), (v(nv - 1), ('c', int(kind == 'chain_unsat')))]
    else:
        nv = n
        pairs = []
        for i in range(n):
            x, y = v(i), v((i + 1) % n)
            if kind == 'union_cycle':
                pairs.append((('+', x, y), a))
            elif kind == 'hom_cycle':
                pairs.append((('+', ('h', 0, x), y), ('+', ('h', 0, a), a)))
            elif kind == 'E_cycle':
                pairs.append((('+', ('e', x), y), ('+', ('e', a), a)))
            elif kind == 'mixed_cycle':
                pairs.append((('+', ('h', 0, x), ('e', y)),
                              ('+', ('h', 0, a), ('e', a))))
            else:
                raise ValueError(kind)
    expected = kind != 'chain_unsat'
    if expected:
        sigma = [a] * nv
        assert all(fuzz.normal(l, sigma) == fuzz.normal(r, sigma) for l, r in pairs)
    # Check that the variable-incidence graph really is one connected component.
    adj = [set() for _ in range(nv)]
    for l, r in pairs:
        vs = {t[1] for s in (l, r) for t in fuzz.walk(s) if t[0] == 'v'}
        for i in vs:
            adj[i].update(vs)
    reached, work = set(), [0]
    while work:
        i = work.pop()
        if i not in reached:
            reached.add(i)
            work.extend(adj[i] - reached)
    assert len(reached) == nv
    encoded = [[fuzz.prefix(l), fuzz.prefix(r)] for l, r in pairs]
    assert len(encoded) == n and len({tuple(q) for q in encoded}) == n
    return dict(id=f'{kind}/{n}', family=kind, equations=n, variables=nv,
                problem=encoded, expected=expected, connected=True,
                justification='Every variable maps to c:0' if expected else
                'The equality chain forces c:0 = c:1, impossible in the free algebra')

families = ['chain_sat', 'chain_unsat', 'union_cycle', 'hom_cycle', 'E_cycle', 'mixed_cycle']
cases = [make_case(f, n) for n in [100, 200] for f in families]
(OUT / 'cases.json').write_text(json.dumps(cases, indent=2) + '\n')
(OUT / 'metadata.json').write_text(json.dumps(dict(
    executable=str(EXE), executable_sha256=hashlib.sha256(EXE.read_bytes()).hexdigest(),
    cutoff_s=LIMIT, repeats=REPEATS, mode='decision', platform=platform.platform(),
    timing='Existing fresh-process, post-parse handshake harness; preprocessing included',
    interpretation='Six deliberately simple connected families, two sizes, repeated identical inputs; not statistical sampling of workloads',
    job_order_seed=20260910), indent=2) + '\n')
for _ in range(3):
    r = fuzz.measure(EXE, dict(problem=[['v:0', 'c:0']], variables=1, expected=True), 'decision', LIMIT)
    assert r['status'] == 'ok', r
jobs = [(c, r) for c in cases for r in range(REPEATS)]
random.Random(20260910).shuffle(jobs)
results = []
started = time.monotonic()
with (OUT / 'runs.jsonl').open('x') as stream:
    for i, (case, repeat) in enumerate(jobs, 1):
        r = dict(id=case['id'], repeat=repeat, **fuzz.measure(EXE, case, 'decision', LIMIT))
        results.append(r)
        stream.write(json.dumps(r) + '\n')
        stream.flush()
        print(json.dumps(dict(done=i, total=len(jobs), elapsed_s=round(time.monotonic()-started, 1), **r)), flush=True)
        if r['status'] == 'mismatch':
            raise RuntimeError(r)
summary = []
for c in cases:
    rs = [r for r in results if r['id'] == c['id']]
    times = [r['elapsed_ns'] / 1e6 for r in rs if r['status'] == 'ok']
    summary.append(dict(id=c['id'], equations=c['equations'], variables=c['variables'],
                        expected=c['expected'], statuses=dict(collections.Counter(r['status'] for r in rs)),
                        completed_median_ms=statistics.median(times) if times else None))
(OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary), flush=True)
