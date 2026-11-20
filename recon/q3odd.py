# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "numpy==2.3.4",
# ]
# ///
"""Reconnaissance: E8 ⊕ E8 against D16⁺ modulo an odd q.

Evidence, not proof. `lake build` remains the only definition of done.

Both lattices sit in ½ℤ¹⁶ with index a power of two over ℤ¹⁶, so for
odd q the class of x in L/qL is the residue of y = 2x in (ℤ/q)¹⁶.
Vectors are enumerated as y: all coordinates of one parity, with
Σy ≡ 0 (mod 4) on each block (D8⁺ twice, or D16⁺).

Two distinct vectors of norm m congruent mod q have 2q² ≤ |u − v|² ≤ 4m,
so classes are singletons below norm q²/2. The datum is the multiset
of class profiles (n_c(m))_m over the classes c met, and its power
sums Σ_c ∏ n_c(m_i).
"""

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

import numpy as np

DATA = Path(__file__).parent / "data"


def ball(n, budget, values=None):
    """All y in ℤⁿ with |y|² ≤ budget and coordinates in `values`."""
    r = int(np.sqrt(budget))
    values = range(-r, r + 1) if values is None else values
    vecs = np.zeros((1, 0), dtype=np.int8)
    rest = np.array([budget])
    for _ in range(n):
        parts_v, parts_r = [], []
        for t in values:
            keep = rest >= t * t
            v = vecs[keep]
            parts_v.append(np.hstack([v, np.full((len(v), 1), t, dtype=np.int8)]))
            parts_r.append(rest[keep] - t * t)
        vecs, rest = np.vstack(parts_v), np.concatenate(parts_r)
    return vecs


def dplus(n, norm_bound):
    """Vectors y = 2x of D_n⁺ (n ≡ 0 mod 8) with |x|² ≤ norm_bound."""
    budget = 4 * norm_bound
    even = 2 * ball(n, budget // 4)
    even = even[(even.sum(1) // 2) % 2 == 0]
    r = int(np.sqrt(budget))
    odd = ball(n, budget, [t for t in range(-r, r + 1) if t % 2])
    odd = odd[odd.sum(1) % 4 == 0]
    return np.vstack([even, odd])


def e8e8(norm_bound):
    e8 = dplus(8, norm_bound)
    nrm = (e8.astype(np.int32) ** 2).sum(1) // 4
    out = []
    for a in range(norm_bound + 1):
        left = e8[nrm == a]
        right = e8[nrm <= norm_bound - a]
        out.append(
            np.hstack([np.repeat(left, len(right), 0), np.tile(right, (len(left), 1))])
        )
    return np.vstack(out)


def profiles(y, q, norms):
    nrm = (y.astype(np.int32) ** 2).sum(1) // 4
    keep = np.isin(nrm, norms)
    y, nrm = y[keep], nrm[keep]
    code = (
        (y.astype(np.int64) % q) * (q ** np.arange(y.shape[1], dtype=np.int64))
    ).sum(1)
    _, inv = np.unique(code, return_inverse=True)
    cols = [np.bincount(inv[nrm == m], minlength=inv.max() + 1) for m in norms]
    return np.stack(cols, 1)


def power_sums(prof, order):
    k = prof.shape[1]
    out = {}
    for combo in itertools.combinations_with_replacement(range(k), order):
        out[combo] = int(np.prod(prof[:, list(combo)].astype(object), 1).sum())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=3)
    ap.add_argument("--bound", type=int, default=8)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    norms = list(range(2, args.bound + 1, 2))
    lat = {"e8e8": e8e8(args.bound), "d16plus": dplus(16, args.bound)}
    prof = {k: profiles(v, args.q, norms) for k, v in lat.items()}
    multiset = {
        k: Counter(map(tuple, p[(p > 1).any(1)].tolist())) for k, p in prof.items()
    }
    result = {
        "q": args.q,
        "norms": norms,
        "shell_sizes": {k: p.sum(0).tolist() for k, p in prof.items()},
        "profile_equal": multiset["e8e8"] == multiset["d16plus"],
        "nonsingleton_profiles": {
            k: sorted([list(t), c] for t, c in m.items()) for k, m in multiset.items()
        },
        "power_sum_differences": {},
    }
    for order in range(2, 7):
        a, b = power_sums(prof["e8e8"], order), power_sums(prof["d16plus"], order)
        diff = {
            "+".join(str(norms[i]) for i in c): a[c] - b[c] for c in a if a[c] != b[c]
        }
        result["power_sum_differences"][order] = diff
    print(json.dumps(result, indent=1))
    if args.write:
        path = DATA / f"q3_odd_e8e8_d16plus_q{args.q}_n{args.bound}.json"
        path.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
