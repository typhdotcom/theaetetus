"""Reconnaissance: theta-equivalent classes in definite genera, by Siegel degree.

Evidence, not proof. `lake build` remains the only definition of done.
Run under Sage: `sage -python recon/q3genus.py`.

For every positive definite genus of rank `n` and determinant `d` in
range, the classes come from Kneser neighbours (Sage), the theta
series to `--theta-bound` from PARI `qfrep`. Classes with equal
truncated theta series are then compared in degree two: the counts of
ordered pairs `(x, y)` with `Q(x) = a`, `Q(y) = c`, `B(x, y) = b` for
`a, c ≤ --pair-bound`, the representation numbers of binary Gram
matrices. Both bounds are raised past the genus's largest basis
norm, which bounds every last successive minimum. A group equal in degree two is a test case for residue data
beyond degree two.
"""

import argparse
import json
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

from sage.all import ZZ, matrix, pari
from sage.quadratic_forms.genera.genus import genera

DATA = Path(__file__).parent / "data"


def theta(gram, bound):
    return [1] + [int(c) for c in pari(gram).qfrep(bound, 0)]


def short(gram, bound):
    """All nonzero vectors of norm ≤ bound, as integer tuples."""
    _, _, vs = pari(gram).qfminim(bound)
    vs = [tuple(int(e) for e in v) for v in vs]
    return vs + [tuple(-e for e in v) for v in vs]


def degree_two(gram, bound):
    g = [[int(e) for e in row] for row in gram.rows()]
    n = len(g)
    vs = short(gram, bound)
    gv = [[sum(g[i][j] * v[j] for j in range(n)) for i in range(n)] for v in vs]
    norm = [sum(a * b for a, b in zip(v, w)) for v, w in zip(vs, gv)]
    hist = Counter()
    for i, w in enumerate(gv):
        for j, v in enumerate(vs):
            hist[(norm[i], norm[j], sum(a * b for a, b in zip(w, v)))] += 1
    return hist


def survey_det(job):
    rank, det, even, theta_bound, pair_bound = job
    out = []
    for G in genera((rank, 0), det, even=even):
        reps = G.representatives(backend="sage")
        if len(reps) < 2:
            continue
        # Truncation only merges classes, so a bound below the last
        # successive minimum fakes equality. The largest diagonal entry of
        # any basis bounds that minimum, so scale both bounds past it.
        top = max(max(int(e) for e in r.diagonal()) for r in reps)
        tb, pb = max(theta_bound, 3 * top), max(pair_bound, top + 12)
        groups = {}
        for r in reps:
            groups.setdefault(tuple(theta(r, tb)), []).append(r)
        for group in groups.values():
            if len(group) < 2:
                continue
            hists = [degree_two(r, pb) for r in group]
            classes = {}
            for r, h in zip(group, hists):
                classes.setdefault(frozenset(h.items()), []).append(r)
            out.append(
                {
                    "rank": rank,
                    "det": det,
                    "even": even,
                    "classes": len(reps),
                    "theta_bound": tb,
                    "pair_bound": pb,
                    "theta_group": [
                        [list(map(int, row)) for row in r.rows()] for r in group
                    ],
                    "degree_two_groups": [len(v) for v in classes.values()],
                }
            )
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rank", type=int, default=4)
    ap.add_argument("--max-det", type=int, default=2000)
    ap.add_argument("--odd", action="store_true", help="odd lattices instead of even")
    ap.add_argument("--theta-bound", type=int, default=80)
    ap.add_argument("--pair-bound", type=int, default=24)
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    even = not args.odd
    jobs = [
        (args.rank, d, even, args.theta_bound, args.pair_bound)
        for d in range(1, args.max_det + 1)
    ]
    start, found = time.time(), []
    with Pool(args.jobs) as pool:
        for rows in pool.imap_unordered(survey_det, jobs, chunksize=4):
            for row in rows:
                found.append(row)
                print(
                    row["det"],
                    len(row["theta_group"]),
                    row["degree_two_groups"],
                    flush=True,
                )
    found.sort(key=lambda r: r["det"])
    result = {
        "rank": args.rank,
        "even": even,
        "max_det": args.max_det,
        "theta_bound": args.theta_bound,
        "pair_bound": args.pair_bound,
        "theta_equal_groups": len(found),
        "degree_two_equal": [r for r in found if max(r["degree_two_groups"]) > 1],
        "theta_groups": found,
        "seconds": round(time.time() - start),
    }
    print(
        json.dumps(
            {k: v for k, v in result.items() if k not in ("theta_groups",)}, indent=1
        )
    )
    if args.write:
        kind = "even" if even else "odd"
        path = DATA / f"q3_genus_rank{args.rank}_{kind}_d{args.max_det}.json"
        path.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
