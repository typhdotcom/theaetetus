# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "numpy==2.3.4",
# ]
# ///
"""Reconnaissance: root configurations of a theta-equivalent pair.

Evidence, not proof. `lake build` remains the only definition of done.

Counts ordered tuples of roots of `E8 ⊕ E8` and `D16⁺` (both have the
480 roots of their root systems) with a prescribed Gram matrix: the
degree-`k` representation numbers at Cartan matrices. Degree-`≤ 3`
configurations agree; `D4` and `A4` split by `±ΔN₄`, the coefficient
of the classwise degree-four law in `q3field.py`.
"""

import itertools
import json
import sys
from pathlib import Path

import numpy as np

DATA = Path(__file__).parent / "data"


def e8_roots():
    out = []
    for i, j in itertools.combinations(range(8), 2):
        for a in (1, -1):
            for b in (1, -1):
                v = np.zeros(8)
                v[i], v[j] = a, b
                out.append(v)
    for s in itertools.product((0.5, -0.5), repeat=8):
        if sum(x < 0 for x in s) % 2 == 0:
            out.append(np.array(s))
    return np.array(out)


def e8sq_roots():
    r = e8_roots()
    z = np.zeros_like(r)
    return np.vstack([np.hstack([r, z]), np.hstack([z, r])])


def d16_roots():
    out = []
    for i, j in itertools.combinations(range(16), 2):
        for a in (1, -1):
            for b in (1, -1):
                v = np.zeros(16)
                v[i], v[j] = a, b
                out.append(v)
    return np.array(out)


def count(roots, gram):
    """Ordered tuples of roots with the given Gram matrix."""
    pairing = np.rint(roots @ roots.T).astype(int)
    size, k = len(roots), len(gram)
    total = 0

    def rec(chosen):
        nonlocal total
        m = len(chosen)
        cand = np.ones(size, bool)
        for a, ia in enumerate(chosen):
            cand &= pairing[ia] == gram[a][m]
        if m == k - 1:
            total += int(cand.sum())
            return
        for c in np.nonzero(cand)[0]:
            rec(chosen + [c])

    rec([])
    return total


CONFIGS = {
    "A1": [[2]],
    "A2": [[2, -1], [-1, 2]],
    "A3": [[2, -1, 0], [-1, 2, -1], [0, -1, 2]],
    "D4": [[2, -1, -1, -1], [-1, 2, 0, 0], [-1, 0, 2, 0], [-1, 0, 0, 2]],
    "A4": [[2, -1, 0, 0], [-1, 2, -1, 0], [0, -1, 2, -1], [0, 0, -1, 2]],
}


def main():
    write = "--write" in sys.argv
    rows = {}
    for name, gram in CONFIGS.items():
        a, b = count(e8sq_roots(), gram), count(d16_roots(), gram)
        rows[name] = dict(gram=gram, e8e8=a, d16plus=b, difference=a - b)
        print(name, a, b, a - b, file=sys.stderr)
    record = dict(
        configurations=rows, delta_n4_from_q3field=5160960, numpy=np.__version__
    )
    text = json.dumps(record, indent=2) + "\n"
    if write:
        (DATA / "q3_root_configurations.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
