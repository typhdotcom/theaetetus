# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "numpy==2.3.4",
# ]
# ///
"""Reconnaissance: residue-refined data on a theta-equivalent pair.

Evidence, not proof. `lake build` remains the only definition of done.

The question. Scalar data sees exactly theta-equivalence: two
lattices with the same theta series have the same defect field at
every scale. The refined datum is the family of coset theta series
on `L / qL`,

    Theta_{c + qL}(t) = sum_{x in c + qL} t^{Q(x)},

and its isometry-invariant shadow is the multiset of these series
over the classes `c`. This script computes that multiset, truncated
at an energy bound, for theta-equivalent non-isometric pairs, and
reports whether it separates them.

Truncated coset counts are exact integers, so a separation found
here is a finite, checkable fact: a count of lattice vectors of
bounded norm in one residue class.
"""

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

import numpy as np

DATA = Path(__file__).parent / "data"


def e8_gram():
    """Cartan matrix of E8 (Bourbaki labelling)."""
    edges = [(0, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]
    g = 2 * np.eye(8, dtype=np.int64)
    for i, j in edges:
        g[i, j] = g[j, i] = -1
    return g


def d16plus_gram():
    """D16 basis with e1 - e2 replaced by the glue (1/2)^16; det 1."""
    eye = np.eye(16)
    basis = [eye[i] - eye[i + 1] for i in range(1, 15)]
    basis += [eye[14] + eye[15], np.full(16, 0.5)]
    b = np.array(basis)
    g = b @ b.T
    assert np.allclose(g, np.round(g))
    return np.round(g).astype(np.int64)


def block(*grams):
    n = sum(g.shape[0] for g in grams)
    out = np.zeros((n, n), dtype=np.int64)
    k = 0
    for g in grams:
        m = g.shape[0]
        out[k : k + m, k : k + m] = g
        k += m
    return out


FORMS = {
    "e8e8": lambda: block(e8_gram(), e8_gram()),
    "d16plus": d16plus_gram,
}


def enumerate_short(gram, bound):
    """All x in Z^n with x^T G x <= bound, as (points, norms).

    Fincke-Pohst on the Cholesky factor, last coordinate vectorized.
    Norms are recomputed exactly in integers; the float recursion only
    prunes, with a safety margin.
    """
    n = gram.shape[0]
    r = np.linalg.cholesky(gram.astype(float)).T  # G = R^T R, R upper
    diag = np.diag(r) ** 2
    mu = r / np.diag(r)[:, None]  # mu[i, j] = r[i, j] / r[i, i]
    eps = 1e-9
    out = []
    x = np.zeros(n, dtype=np.int64)

    def rec(i, rem):
        center = -float(mu[i, i + 1 :] @ x[i + 1 :])
        half = np.sqrt(max(rem, 0.0) / diag[i]) + eps
        lo, hi = int(np.ceil(center - half)), int(np.floor(center + half))
        if i == 0:
            if lo > hi:
                return
            block_ = np.repeat(x[None, :], hi - lo + 1, axis=0)
            block_[:, 0] = np.arange(lo, hi + 1)
            out.append(block_)
            return
        for v in range(lo, hi + 1):
            x[i] = v
            rec(i - 1, rem - diag[i] * (v - center) ** 2 + eps)
        x[i] = 0

    rec(n - 1, bound + eps)
    pts = np.concatenate(out)
    norms = np.einsum("ij,jk,ik->i", pts, gram, pts)
    keep = norms <= bound
    return pts[keep], norms[keep]


def theta_counts(norms, bound):
    c = Counter(norms.tolist())
    return [c.get(k, 0) for k in range(bound + 1)]


def coset_profile(pts, norms, q, bound):
    """Per class of L/qL met by a vector of norm <= bound, its truncated
    theta series; returned as the multiset of those series."""
    n = pts.shape[1]
    weights = np.array([q**k for k in range(n)], dtype=object)
    keys = (np.mod(pts, q).astype(object) * weights).sum(axis=1)
    per = {}
    for key, nm in zip(keys.tolist(), norms.tolist()):
        row = per.setdefault(key, [0] * (bound + 1))
        row[nm] += 1
    return Counter(tuple(v) for v in per.values())


def summarize(profile, bound):
    """Classes by (minimal norm, number of minimal vectors)."""
    shape = Counter()
    for series, mult in profile.items():
        m = next(k for k, c in enumerate(series) if c)
        shape[(m, series[m])] += mult
    return sorted(shape.items())


def run(pair, q, bound):
    rows = {}
    for name in pair:
        gram = FORMS[name]()
        assert round(np.linalg.det(gram)) == 1
        pts, norms = enumerate_short(gram, bound)
        prof = coset_profile(pts, norms, q, bound)
        rows[name] = dict(
            theta=theta_counts(norms, bound),
            classes_met=sum(prof.values()),
            profile=prof,
            shape=summarize(prof, bound),
        )
    a, b = (rows[p] for p in pair)
    return rows, a["theta"] == b["theta"], a["profile"] == b["profile"]


def falling_moments(profile, norm, kmax):
    """sum over classes of n (n-1) ... (n-k+1), n = vectors of the given
    norm in the class: ordered k-tuples of distinct vectors of that norm
    in one class. Each is a count of k-tuples (x, y_2, ..., y_k) in L^k
    with Q(x) = Q(x + 2 y_i) = norm and a distinctness condition, so it is
    determined by the degree-k Siegel theta series."""
    out = []
    for k in range(1, kmax + 1):
        total = 0
        for series, mult in profile.items():
            n, f = series[norm], 1
            for j in range(k):
                f *= n - j
            total += mult * f
        out.append(total)
    return out


def separating_shapes(rows, pair):
    a, b = (dict(rows[p]["shape"]) for p in pair)
    keys = sorted(set(a) | set(b))
    return [
        dict(
            min_norm=k[0],
            min_count=k[1],
            **{p: d.get(k, 0) for p, d in zip(pair, (a, b))},
        )
        for k in keys
        if a.get(k, 0) != b.get(k, 0)
    ]


def cmd_selftest(_):
    # E8 x E8 and D16+ share the theta series E4^2 = 1 + 480q + 61920q^2 + ...
    expected = [1, 0, 480, 0, 61920]
    for name in FORMS:
        _, norms = enumerate_short(FORMS[name](), 4)
        got = theta_counts(norms, 4)
        assert got == expected, (name, got)
    print("selftest ok")


def cmd_pair(args):
    pair = ("e8e8", "d16plus")
    rows, same_theta, same_profile = run(pair, args.q, args.bound)
    record = dict(
        pair=list(pair),
        q=args.q,
        bound=args.bound,
        theta={p: rows[p]["theta"] for p in pair},
        theta_equal=same_theta,
        coset_profile_equal=same_profile,
        classes_met={p: rows[p]["classes_met"] for p in pair},
        separating_shapes=separating_shapes(rows, pair),
        falling_moments={
            str(m): {p: falling_moments(rows[p]["profile"], m, 6) for p in pair}
            for m in range(2, args.bound + 1, 2)
        },
        numpy=np.__version__,
    )
    text = json.dumps(record, indent=2) + "\n"
    if args.write:
        path = DATA / f"q3_e8e8_d16plus_q{args.q}_n{args.bound}.json"
        path.write_text(text)
        print(f"wrote {path}", file=sys.stderr)
    print(text, end="")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(required=True)
    sub.add_parser("selftest").set_defaults(fn=cmd_selftest)
    p = sub.add_parser("pair", help="E8+E8 versus D16+")
    p.add_argument("--q", type=int, default=2)
    p.add_argument("--bound", type=int, default=4)
    p.add_argument("--write", action="store_true")
    p.set_defaults(fn=cmd_pair)
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
