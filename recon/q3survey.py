# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "numpy==2.3.4",
# ]
# ///
"""Reconnaissance: does mod-q coset data separate every theta-equivalent pair?

Evidence, not proof. `lake build` remains the only definition of done.

Conway and Sloane's quaternary family `L∓(a, b, c, d)`: Gram
`Mᵀ·diag(a, b, c, d)·M / 12` for the two change-of-basis matrices
`M∓` below (at `(1, 7, 13, 19)` these are Schiemann's pair). For each
parameter tuple giving two integral Gram matrices, the survey checks

  * theta equality through an energy bound,
  * isometry (a backtracking search for a basis of one lattice inside
    the other with the other's Gram matrix),
  * for each modulus `q`, whether the multisets of truncated coset
    theta series on `L/qL` agree, at a bound where classes can hold
    two vectors (from `q²·λ₁/4`, doubling until separated or a cap),

and records the smallest separating modulus, and the falling moment
order at which the separating class counts first differ. A pair that
is theta-equivalent, non-isometric, and unseparated at every modulus
tried is the event the survey exists to find.
"""

import itertools
import json
import sys
from math import gcd
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from q3 import coset_profile, enumerate_short, falling_moments, theta_counts  # noqa: E402

DATA = Path(__file__).parent / "data"

M_MINUS = np.array([[-3, 1, 1, 1], [-1, -3, -1, 1], [-1, 1, -3, -1], [-1, -1, 1, -3]])
M_PLUS = np.array([[3, 1, 1, 1], [-1, 3, -1, 1], [-1, 1, 3, -1], [-1, -1, 1, 3]])

SURVEY_CONFIG = dict(
    max_param=50,
    theta_bound=400,
    moduli=[2, 3, 4, 5, 7, 11, 13],
    min_bound=40,
    max_bound=1600,
)


def family(a, b, c, d):
    out = []
    for m in (M_MINUS, M_PLUS):
        g = m.T @ np.diag([a, b, c, d]) @ m
        if np.any(g % 12):
            return None
        out.append(g // 12)
    return out


def isometric(g1, g2):
    """Search for vectors of L1 with Gram matrix g2 forming a basis."""
    n = len(g2)
    pts, norms = enumerate_short(g1, int(max(np.diag(g2))))
    by_norm = {}
    for p, m in zip(pts, norms):
        by_norm.setdefault(int(m), []).append(p)

    def rec(chosen):
        k = len(chosen)
        if k == n:
            return abs(round(np.linalg.det(np.array(chosen, dtype=float)))) == 1
        for v in by_norm.get(int(g2[k, k]), []):
            if all(int(v @ g1 @ w) == int(g2[k, j]) for j, w in enumerate(chosen)):
                if rec(chosen + [v]):
                    return True
        return False

    return rec([])


def first_moment_split(pa, pb, bound):
    for m in range(1, bound + 1):
        fa, fb = falling_moments(pa, m, 6), falling_moments(pb, m, 6)
        if fa != fb:
            k = next(i for i in range(6) if fa[i] != fb[i])
            return dict(energy=m, order=k + 1)
    return None


def survey():
    cfg = SURVEY_CONFIG
    rows = []
    for a, b, c, d in itertools.combinations(range(1, cfg["max_param"] + 1), 4):
        if gcd(gcd(a, b), gcd(c, d)) != 1:
            continue
        pair = family(a, b, c, d)
        if pair is None:
            continue
        g1, g2 = pair
        t1 = theta_counts(
            enumerate_short(g1, cfg["theta_bound"])[1], cfg["theta_bound"]
        )
        t2 = theta_counts(
            enumerate_short(g2, cfg["theta_bound"])[1], cfg["theta_bound"]
        )
        row = dict(
            params=[a, b, c, d], det=int(round(np.linalg.det(g1))), theta_equal=t1 == t2
        )
        if not row["theta_equal"]:
            rows.append(row)
            continue
        row["isometric"] = isometric(g1, g2)
        if row["isometric"]:
            rows.append(row)
            continue
        lam = min(int(g1[i, i]) for i in range(4))
        row["moduli"] = {}
        for q in cfg["moduli"]:
            bound = max(cfg["min_bound"], (q * q * lam + 3) // 4 + 20)
            while True:
                p1, n1 = enumerate_short(g1, bound)
                p2, n2 = enumerate_short(g2, bound)
                pa, pb = (
                    coset_profile(p1, n1, q, bound),
                    coset_profile(p2, n2, q, bound),
                )
                colliding = sum(mult for s, mult in pa.items() if sum(s) >= 2)
                if pa != pb or 2 * bound > cfg["max_bound"]:
                    break
                bound *= 2
            entry = dict(bound=bound, colliding_classes=colliding, separated=pa != pb)
            if pa != pb:
                entry["split"] = first_moment_split(pa, pb, bound) or "joint"
            row["moduli"][str(q)] = entry
        seps = [int(q) for q, v in row["moduli"].items() if v["separated"]]
        row["first_separating_modulus"] = min(seps) if seps else None
        rows.append(row)
        print(
            row["params"],
            row.get("first_separating_modulus"),
            file=sys.stderr,
            flush=True,
        )
    return rows


def main():
    rows = survey()
    tested = [r for r in rows if r["theta_equal"] and not r.get("isometric")]
    summary = dict(
        tuples=len(rows),
        theta_unequal=sum(1 for r in rows if not r["theta_equal"]),
        isometric=sum(1 for r in rows if r.get("isometric")),
        tested=len(tested),
        unseparated=[
            r["params"] for r in tested if r["first_separating_modulus"] is None
        ],
        first_modulus_histogram={},
        split_order_histogram={},
    )
    for r in tested:
        k = str(r["first_separating_modulus"])
        summary["first_modulus_histogram"][k] = (
            summary["first_modulus_histogram"].get(k, 0) + 1
        )
        q = r["first_separating_modulus"]
        if q is not None:
            s = r["moduli"][str(q)]["split"]
            o = "joint" if s == "joint" else str(s["order"])
            summary["split_order_histogram"][o] = (
                summary["split_order_histogram"].get(o, 0) + 1
            )
    record = dict(
        config=SURVEY_CONFIG, summary=summary, rows=rows, numpy=np.__version__
    )
    text = json.dumps(record, indent=1) + "\n"
    if "--write" in sys.argv:
        (DATA / "q3_survey_conway_sloane.json").write_text(text)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
