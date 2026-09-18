#!/usr/bin/env python3
"""Reproducible, process-isolated grammar sampling. Python standard library only.

The independent ground normalizer checks planted witnesses, never supplies an
answer to the solver. Timeouts remain unknown, including in the random cohort.
"""

import argparse
import collections
import datetime
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import platform
import random
import select
import signal
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def term(rng, size, profile, variables=2):
    if size == 1:
        choices = [("0",), ("c", 0), ("c", 1)]
        choices += [("v", v) for v in range(variables)]
        return rng.choice(choices)
    operators = (["h"] if profile == "h" else ["e"] if profile == "E" else ["h", "e"])
    if size >= 3:
        operators += ["+", "+"]
    op = rng.choice(operators)
    if op == "+":
        left = rng.randint(1, size - 2)
        return (op, term(rng, left, profile, variables), term(rng, size - 1 - left, profile, variables))
    child = term(rng, size - 1, profile, variables)
    return (op, rng.randrange(2), child) if op == "h" else (op, child)


def children(t):
    return t[1:] if t[0] == "+" else (t[-1],) if t[0] in ("h", "e") else ()


def walk(t):
    yield t
    for child in children(t):
        yield from walk(child)


def force_variable(t, rng, variables):
    if any(a[0] == "v" for a in walk(t)):
        return t
    if not children(t):
        return ("v", rng.randrange(variables))
    if t[0] == "+":
        return ("+", force_variable(t[1], rng, variables), t[2])
    return (*t[:-1], force_variable(t[-1], rng, variables))


def substitute(t, sigma):
    if t[0] == "v":
        return sigma[t[1]]
    if t[0] == "+":
        return ("+", substitute(t[1], sigma), substitute(t[2], sigma))
    if t[0] in ("e", "h"):
        return (*t[:-1], substitute(t[-1], sigma))
    return t


def normal(t, sigma=None):
    """Independent ground NF: sets of (word, constant-or-recursive-E-child)."""
    op = t[0]
    if op == "0":
        return frozenset()
    if op == "c":
        return frozenset([((), ("c", t[1]))])
    if op == "v":
        if sigma is None:
            raise ValueError("normal requires a ground term or planted substitution")
        return normal(sigma[t[1]])
    if op == "+":
        return normal(t[1], sigma) | normal(t[2], sigma)
    child = normal(t[-1], sigma)
    if op == "e":
        return frozenset([((), ("e", child))]) if child else frozenset()
    return frozenset([((t[1],) + word, atom) for word, atom in child])


def rewrite(t, rng):
    """Only unconditional ACUIhE identities; E is never distributed."""
    if t[0] == "+":
        a, b = rewrite(t[1], rng), rewrite(t[2], rng)
        t = ("+", b, a) if rng.random() < 0.5 else ("+", a, b)
    elif t[0] in ("e", "h"):
        t = (*t[:-1], rewrite(t[-1], rng))
        if t[0] == "h" and t[2][0] == "+" and rng.random() < 0.5:
            t = ("+", ("h", t[1], t[2][1]), ("h", t[1], t[2][2]))
    if rng.random() < 0.12:
        t = ("+", t, ("0",))
    return t


def prefix(t):
    if t[0] in ("v", "c"):
        return f"{t[0]}:{t[1]}"
    if t[0] == "h":
        return f"h:{t[1]} {prefix(t[2])}"
    return " ".join([t[0]] + [prefix(c) for c in children(t)])


def depth(t, e_only=False):
    return (int(t[0] == "e") if e_only else 1) + max(
        [depth(c, e_only) for c in children(t)] or [0])


def generate(seed, profile, size, equations, family, index):
    key = f"{seed}/{profile}/{size}/{equations}/{family}/{index}"
    case_seed = int.from_bytes(hashlib.sha256(key.encode()).digest()[:8], "big")
    rng = random.Random(case_seed)
    nvars = 2
    sigma = [term(rng, rng.choice([1, 1, 1, 2]), profile, 0) for _ in range(nvars)]
    problem = []
    certificate = {"kind": family}
    if family == "random":
        problem = [(term(rng, size, profile), term(rng, size, profile)) for _ in range(equations)]
        expected = None
    elif family == "unsat" and equations > 1:
        # All variables of the final term are fixed by preceding equations.
        nvars = equations - 1
        sigma = [term(rng, rng.choice([1, 2]), profile, 0) for _ in range(nvars)]
        problem = [(("v", v), sigma[v]) for v in range(nvars)]
        t = force_variable(term(rng, size, profile, nvars), rng, nvars)
        g = substitute(t, sigma)
        problem.append((t, ("+", g, ("c", 2))))
        assert all(a[0] != "c" or a[1] != 2 for a in walk(g))
        assert normal(t, sigma) != normal(problem[-1][1])
        certificate.update(kind="anchored_contradiction", substitution=[prefix(s) for s in sigma])
        expected = False
    else:
        for _ in range(equations):
            t = force_variable(term(rng, size, profile), rng, nvars)
            g = rewrite(substitute(t, sigma), rng)
            problem.append((t, g))
        assert all(normal(a, sigma) == normal(b, sigma) for a, b in problem)
        if family == "sat":
            certificate["substitution"] = [prefix(s) for s in sigma]
            expected = True
        else:
            # A positive fresh root summand cannot disappear under substitution.
            t, g = problem[0]
            problem[0] = (("+", ("c", 2), t), g)
            assert all(a[0] != "v" and (a[0] != "c" or a[1] != 2) for a in walk(g))
            certificate.update(kind="fresh_root_constant", fresh=2)
            expected = False
    terms = [t for pair in problem for t in pair]
    nodes = [a for t in terms for a in walk(t)]
    encoded = [[prefix(a), prefix(b)] for a, b in problem]
    return dict(id=key, case_seed=case_seed, profile=profile, budget=size, equations=equations,
                family=family, sample=index, expected=expected, certificate=certificate,
                problem=encoded, variables=nvars, nodes=len(nodes),
                e_count=sum(a[0] == "e" for a in nodes), h_count=sum(a[0] == "h" for a in nodes),
                depth=max(map(depth, terms)), e_depth=max(depth(t, True) for t in terms),
                distinct_variables=len({a[1] for a in nodes if a[0] == "v"}),
                input_hash=hashlib.sha256(json.dumps(encoded).encode()).hexdigest())


def measure(executable, case, mode, timeout):
    command = [str(executable)]
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True, start_new_session=True)
    start = None
    try:
        process.stdin.write(json.dumps(dict(problem=case["problem"], mode=mode,
                                            variableCount=case["variables"])) + "\n")
        process.stdin.flush()
        if not select.select([process.stdout], [], [], 10)[0]:
            raise RuntimeError("worker startup/parse handshake timed out")
        if process.stdout.readline().strip() != "ready":
            raise RuntimeError("worker did not acknowledge parsed input")
        start = time.perf_counter()
        stdout, stderr = process.communicate("go\n", timeout=timeout)
        wall = time.perf_counter() - start
        if process.returncode:
            return dict(status="error", wall_s=wall, error=stderr[-2000:], returncode=process.returncode)
        result = json.loads(stdout)
        mismatch = case["expected"] is not None and result["answer"] != case["expected"]
        return dict(status="mismatch" if mismatch else "ok", wall_s=wall,
                    **result)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        return dict(status="timeout", wall_s=timeout)
    except Exception as error:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
        _, stderr = process.communicate()
        return dict(status="error", error=str(error), stderr=stderr[-2000:],
                    wall_s=time.perf_counter() - start if start else None)


def wilson(k, n):
    z = 1.959963984540054
    p = k / n
    center = (p + z*z/(2*n))/(1 + z*z/n)
    half = z*math.sqrt(p*(1-p)/n + z*z/(4*n*n))/(1 + z*z/n)
    return [max(0, center-half), min(1, center+half)]


def summarize(cases, results, timeout, seed):
    by_id = {c["id"]: c for c in cases}
    groups = collections.defaultdict(list)
    for r in results:
        c = by_id[r["id"]]
        groups[(c["profile"], c["budget"], c["equations"], c["family"], r["mode"])].append(r)
    summaries = []
    rng = random.Random(seed)
    for key, rows in sorted(groups.items()):
        # Cluster repetitions by input; independent samples are input cases.
        clusters = collections.defaultdict(list)
        for r in rows:
            clusters[r["id"]].append(r)
        errors = [r for r in rows if r["status"] not in ("ok", "timeout")]
        completed = [r for r in rows if r["status"] == "ok"]
        capped = [statistics.mean(min(r["wall_s"], timeout) for r in rr)
                  for rr in clusters.values() if all(r["status"] in ("ok", "timeout") for r in rr)]
        bootstrap = sorted(statistics.mean(rng.choices(capped, k=len(capped))) for _ in range(2000)) if capped else []
        all_complete = sum(all(r["status"] == "ok" for r in rr) for rr in clusters.values())
        elapsed = sorted(r["elapsed_ns"] / 1e6 for r in completed)
        row = dict(zip(("profile", "budget", "equations", "family", "mode"), key))
        row.update(samples=len(clusters), runs=len(rows), complete=len(completed),
                   timeouts=sum(r["status"] == "timeout" for r in rows), errors=len(errors),
                   all_repeats_complete=all_complete,
                   completion_ci95=wilson(all_complete, len(clusters)),
                   completed_median_ms=statistics.median(elapsed) if elapsed else None,
                   completed_p90_ms=elapsed[math.ceil(.9*len(elapsed))-1] if elapsed else None,
                   capped_wall_mean_ms=1000*statistics.mean(capped) if capped else None,
                   capped_wall_ci95_ms=[1000*bootstrap[49], 1000*bootstrap[1949]] if bootstrap else None,
                   answers=dict(collections.Counter(str(r["answer"]).lower() for r in completed)),
                   unique_inputs=len({by_id[k]["input_hash"] for k in clusters}),
                   median_nodes=statistics.median(by_id[k]["nodes"] for k in clusters),
                   median_e_count=statistics.median(by_id[k]["e_count"] for k in clusters))
        summaries.append(row)
    return summaries


def source_fingerprint():
    digest = hashlib.sha256()
    paths = sorted(itertools.chain((ROOT / "ACUIhE").rglob("*.lean"),
                                    (ROOT / "Benchmarks").glob("*.lean"),
                                    (ROOT / "Benchmarks").glob("*.py")))
    paths += [ROOT / "lakefile.toml", ROOT / "lean-toolchain", ROOT / "lake-manifest.json"]
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260910)
    parser.add_argument("--samples", type=int, default=20, help="independent inputs per cell")
    parser.add_argument("--sizes", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument("--equations", type=int, nargs="+", default=[1, 3])
    parser.add_argument("--profiles", nargs="+", choices=["h", "E", "mixed"], default=["h", "E", "mixed"])
    parser.add_argument("--families", nargs="+", choices=["sat", "unsat", "random"], default=["sat", "unsat", "random"])
    parser.add_argument("--modes", nargs="+", choices=["decision", "witness"], default=["decision"])
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=.5)
    parser.add_argument("--executable", type=Path, default=ROOT / ".lake/build/bin/acuihe_bench")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--replay", type=Path, help="reuse cases.jsonl without regenerating inputs")
    source.add_argument("--retry-timeouts", type=Path,
                        help="replay only timed-out inputs from a completed single-run decision directory")
    args = parser.parse_args()
    if min(args.samples, args.repeats, *args.sizes, *args.equations) < 1 or args.timeout <= 0:
        parser.error("counts, budgets and timeout must be positive")
    args.executable = args.executable.resolve()
    executable_hash = hashlib.sha256(args.executable.read_bytes()).hexdigest()
    selection = None
    if args.retry_timeouts:
        previous = args.retry_timeouts
        prior_meta = json.loads((previous / "metadata.json").read_text())
        prior_cases = [json.loads(s) for s in (previous / "cases.jsonl").read_text().splitlines()]
        prior_runs = [json.loads(s) for s in (previous / "runs.jsonl").read_text().splitlines()]
        prior_args = prior_meta["arguments"]
        if (prior_args["modes"] != ["decision"] or prior_args["repeats"] != 1
                or args.modes != ["decision"] or args.repeats != 1):
            parser.error("timeout follow-up requires one decision run per input in both cohorts")
        if executable_hash != prior_meta["executable_sha256"]:
            parser.error("timeout follow-up must use the same compiled executable")
        if args.timeout <= prior_args["timeout"]:
            parser.error("timeout follow-up requires a longer cutoff")
        by_id = {r["id"]: r for r in prior_runs}
        case_ids = {c["id"] for c in prior_cases}
        if (len(by_id) != len(prior_runs) or len(case_ids) != len(prior_cases)
                or set(by_id) != case_ids
                or any(r["status"] not in ("ok", "timeout") or r["mode"] != "decision"
                       or r["repeat"] != 0 for r in prior_runs)):
            parser.error("prior decision cohort is incomplete, duplicated, or contains errors")
        cases = [c for c in prior_cases if by_id[c["id"]]["status"] == "timeout"]
        selection = dict(kind="prior_timeouts_only", prior_directory=str(previous),
                         prior_cutoff_s=prior_args["timeout"], prior_cases=len(prior_cases),
                         prior_completed=sum(r["status"] == "ok" for r in prior_runs),
                         interpretation="conditional follow-up; not a fresh random sample or full-cohort rerun")
    elif args.replay:
        cases = [json.loads(line) for line in args.replay.read_text().splitlines()]
    else:
        cases = [generate(args.seed, *cell, i) for cell in itertools.product(
            args.profiles, args.sizes, args.equations, args.families) for i in range(args.samples)]
    if not cases:
        parser.error("no inputs selected")
    args.output.mkdir(parents=True, exist_ok=False)
    metadata = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    arguments={k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                    platform=platform.platform(), machine=platform.machine(), python=platform.python_version(),
                    cpu_count=os.cpu_count(), lean_toolchain=(ROOT/"lean-toolchain").read_text().strip(),
                    executable_sha256=executable_hash,
                    source_sha256=source_fingerprint(), cases=len(cases),
                    selection=selection,
                    sampling="seeded recursive grammar, not uniform over terms or semantic equivalence classes",
                    timing="monotonic Lean solver time; post-handshake wall cutoff; serial fresh processes",
                    memory="not measured: macOS time -l requires a sysctl disallowed by the sandbox")
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    (args.output / "cases.jsonl").write_text("".join(json.dumps(c)+"\n" for c in cases))
    jobs = [(c, mode, repeat) for c in cases for mode in args.modes for repeat in range(args.repeats)]
    random.Random(args.seed ^ 0xA55A).shuffle(jobs)
    # Untimed process warmup, not a statistical observation.
    warmup = dict(problem=[["v:0", "c:0"]], variables=1, expected=True)
    for _ in range(3):
        result = measure(args.executable, warmup, "decision", 10)
        if result["status"] != "ok":
            raise RuntimeError(f"warmup failed: {result}")
    results = []
    started = time.monotonic()
    with (args.output / "runs.jsonl").open("w") as stream:
        for i, (case, mode, repeat) in enumerate(jobs, 1):
            result = dict(id=case["id"], mode=mode, repeat=repeat,
                          **measure(args.executable, case, mode, args.timeout))
            results.append(result)
            stream.write(json.dumps(result)+"\n")
            stream.flush()
            if i % 25 == 0 or i == len(jobs) or result["status"] in ("error", "mismatch"):
                counts = dict(collections.Counter(r["status"] for r in results))
                print(json.dumps(dict(done=i, total=len(jobs), elapsed_s=round(time.monotonic()-started, 1),
                                      counts=counts)), flush=True)
            if result["status"] in ("error", "mismatch"):
                raise RuntimeError(f"Stopped; failing case and diagnostic preserved: {result}")
    summary = summarize(cases, results, args.timeout, args.seed)
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(f"Saved {len(results)} measurements to {args.output}", flush=True)


if __name__ == "__main__":
    main()
