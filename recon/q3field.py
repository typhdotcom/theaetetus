# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "mpmath==1.4.1",
#     "numpy==2.3.4",
# ]
# ///
"""Reconnaissance: the classwise defect on a theta-equivalent pair.

Evidence, not proof. `lake build` remains the only definition of done.

For a unimodular lattice `L` and a class `c` of `L / 2L`, the coset
mass and its character twist are

    Theta_c(b) = sum_{x in c + 2L} exp(-b |x|^2),
    What_c(b)  = sum_{u in L} (-1)^<u, c> exp(-b |u|^2),

and Poisson summation over `2L` gives, for the same class,

    Theta_c(b) = 2^-n (pi/b)^(n/2) What_c(pi^2 / (4b)).

The classwise defect is the four-term cross-ratio of `log Theta_c`
along the dilation tower,

    D_c(q, q')_s = log Theta_c(q^2 s) + log Theta_c(q'^2 s)
                   - log Theta_c(g^2 s) - log Theta_c(l^2 s),

`g = gcd`, `l = lcm`; the class `0` carries the scalar defect of `2L`,
and the classes sum to the scalar mass, `sum_c Theta_c = Z_L`. The
Poisson prefactor has weight zero in the cross-ratio, so the
classwise field reflects onto the twisted one:

    D_c(q, q')_s = Dhat_c(q/g, q'/g)_t,    t = pi^2 / (4 s l^2).

Both lattices here are `D_n^+` or sums of them, so every mass is a
sum of four products of one-dimensional theta sums (the parity
character on `D_n`), evaluated to working precision with no
enumeration cutoff. The twisted masses are computed from their own
product formula, not through Poisson, so the reflection law is an
independent check of the engine.
"""

import argparse
import itertools
import json
import sys
from functools import cache
from math import gcd
from pathlib import Path

import mpmath as mp
import numpy as np

DATA = Path(__file__).parent / "data"

SWEEP_CONFIG = dict(
    dps=40,
    pairs=[[2, 3], [2, 5], [3, 5], [4, 6]],
    scales=["0.01", "0.03", "0.1", "0.3", "1", "3"],
    moments=6,
    twist_digit_cap=300,
    asymptotic_pair=[2, 3],
    asymptotic_t=["3", "4", "5", "6", "7", "8"],
)


def dplus_basis2(n):
    """Basis of D_n^+ in doubled coordinates: the D_n basis with
    e1 - e2 replaced by the glue (1/2)^n."""
    eye = 2 * np.eye(n, dtype=np.int64)
    rows = [eye[i] - eye[i + 1] for i in range(1, n - 1)]
    rows += [eye[n - 2] + eye[n - 1], np.ones(n, dtype=np.int64)]
    b = np.array(rows)
    assert round(abs(np.linalg.det(b / 2))) == 1
    return b


def classes2(n):
    """Representatives of D_n^+ / 2 D_n^+ in doubled coordinates."""
    b = dplus_basis2(n)
    bits = np.array(list(itertools.product((0, 1), repeat=n)), dtype=np.int64)
    return bits @ b


class Engine:
    """Masses of D_n^+ cosets and twists at one scale `b`.

    Coset masses split each one-dimensional sum by the parity of its
    index and combine the parts by a parity recursion, so every term is
    positive and no precision is lost to cancellation. Twisted masses
    carry characters and cancel genuinely; the caller supplies the
    extra digits that cancellation costs."""

    def __init__(self, b, extra=0):
        self.b = mp.mpf(b)
        self.extra = extra

    def _tol(self):
        return (mp.mp.dps + 10) * mp.log(10)

    @cache
    def parts(self, a2, step2, w2):
        """(even, odd) parts of sum_k exp(pi i w x_k) exp(-b x_k^2),
        x_k = a + step k, a = a2/2, step = step2/2, w = w2/2."""
        a, step, w = mp.mpf(a2) / 2, mp.mpf(step2) / 2, mp.mpf(w2) / 2
        k0 = int(mp.nint(-a / step))
        tol = self._tol()
        acc = [mp.mpc(0), mp.mpc(0)]
        for direction in (1, -1):
            # terms shrink outward; each parity stops relative to its own
            # leading term on this side
            lead = [None, None]
            k = k0 if direction == 1 else k0 - 1
            while True:
                x = a + step * k
                e = self.b * x * x
                p = k % 2
                if lead[p] is None:
                    lead[p] = e
                if all(v is not None and e - v > tol for v in lead):
                    break
                if e - lead[p] <= tol:
                    acc[p] += mp.expjpi(w * x) * mp.exp(-e)
                k += direction
        return tuple(acc)

    def _dplus(self, a2s, step2, w2s):
        """sum over y in D_n^+ of chi(a + step y) exp(-b |a + step y|^2):
        D_n is the even-sum sublattice of Z^n, D_n^+ adds the glue."""
        total = mp.mpc(0)
        for glue in (0, step2 // 2):
            even, odd = mp.mpc(1), mp.mpc(0)
            for a2, w2 in zip(a2s, w2s):
                e, o = self.parts(a2 + glue, step2, w2)
                even, odd = even * e + odd * o, even * o + odd * e
            total += even
        return total

    @cache
    def coset(self, c2):
        """Theta_c(b) on a D_n^+ factor; c2 sorted doubled coordinates."""
        val = self._dplus(list(c2), 4, [0] * len(c2))
        return val.real

    @cache
    def twist(self, c2):
        """What_c(b) on a D_n^+ factor; c2 sorted doubled coordinates."""
        with mp.extradps(self.extra):
            val = self._dplus([0] * len(c2), 2, list(c2))
            assert abs(val.imag) <= mp.mpf(10) ** (-mp.mp.dps + 5) * (1 + abs(val.real))
            return +val.real


def key(c2):
    return tuple(sorted(int(v) for v in c2))


def masses(form, b, which, extra=0):
    """Per class of L/2L, in a fixed class order, Theta_c or What_c."""
    eng = Engine(b, extra)
    f = eng.coset if which == "coset" else eng.twist
    if form == "d16plus":
        return [f(key(c)) for c in classes2(16)]
    e8 = [f(key(c)) for c in classes2(8)]
    return [x * y for x in e8 for y in e8]


def twist_digits(form, t):
    """Digits the twisted masses at scale t lose to cancellation: their
    terms total Z_L(t), and by Poisson the smallest twisted mass is
    2^n (t/pi)^(n/2) min_c Theta_c(pi^2 / 4t)."""
    z = mp.fsum(masses(form, t, "coset"))
    low = min(masses(form, mp.pi**2 / (4 * t), "coset"))
    small = mp.mpf(2) ** 16 * (t / mp.pi) ** 8 * low
    return max(0, int(mp.ceil(mp.log10(z / small)))) + 10


def roots2(form):
    """Norm-2 vectors in doubled coordinates."""
    out = []
    n = 16 if form == "d16plus" else 8
    for i in range(n):
        for j in range(i + 1, n):
            for si in (2, -2):
                for sj in (2, -2):
                    v = np.zeros(n, dtype=np.int64)
                    v[i], v[j] = si, sj
                    out.append(v)
    if form == "e8e8":
        for signs in itertools.product((1, -1), repeat=8):
            if signs.count(-1) % 2 == 0:
                out.append(np.array(signs, dtype=np.int64))
        zero = np.zeros(8, dtype=np.int64)
        return [np.concatenate([r, zero]) for r in out] + [
            np.concatenate([zero, r]) for r in out
        ]
    return out


def class_index(form, v2):
    """Index of the class of v in the class order used by `masses`."""
    if form == "d16plus":
        bits = np.linalg.solve(dplus_basis2(16).T.astype(float), v2.astype(float))
        bits = np.mod(np.round(bits).astype(np.int64), 2)
        return int("".join(map(str, bits)), 2)
    b8 = dplus_basis2(8).T.astype(float)
    halves = []
    for part in (v2[:8], v2[8:]):
        bits = np.mod(
            np.round(np.linalg.solve(b8, part.astype(float))).astype(np.int64), 2
        )
        halves.append(int("".join(map(str, bits)), 2))
    return halves[0] * 256 + halves[1]


def root_quadruples(form):
    """#{(u1, u2, u3, u4) roots : u1 + u2 + u3 + u4 in 2L}, through the
    Walsh-Hadamard transform of the root count per class (the pairing on
    L/2L is the dot product of basis bits under the Gram matrix mod 2,
    and quadruple counts only need the group law, which is bitwise xor)."""
    counts = np.zeros(2**16, dtype=np.int64)
    for r in roots2(form):
        counts[class_index(form, r)] += 1
    h = counts.astype(object)
    step = 1
    while step < len(h):
        for i in range(0, len(h), 2 * step):
            for j in range(i, i + step):
                x, y = h[j], h[j + step]
                h[j], h[j + step] = x + y, x - y
        step *= 2
    return sum(v**4 for v in h) // 2**16


def selftest(_):
    mp.mp.dps = 30
    b = mp.mpf("0.7")
    for form in ("e8e8", "d16plus"):
        th = masses(form, b, "coset")
        tw = masses(form, b, "twist")
        z = tw[0]
        assert mp.almosteq(mp.fsum(th), z, mp.mpf(10) ** -25), form
        b4 = masses(form, 4 * b, "twist")[0]
        assert mp.almosteq(th[0], b4, mp.mpf(10) ** -25), form
        bp = mp.pi**2 / (4 * b)
        twp = masses(form, bp, "twist")
        pref = mp.mpf(2) ** -16 * (mp.pi / b) ** 8
        err = max(abs(t - pref * w) / t for t, w in zip(th, twp))
        assert err < mp.mpf(10) ** -25, (form, err)
    za = masses("e8e8", b, "twist")[0]
    zb = masses("d16plus", b, "twist")[0]
    assert mp.almosteq(za, zb, mp.mpf(10) ** -25)
    print("selftest ok")


def defect(table, q, qq):
    g = gcd(q, qq)
    l = q * qq // g
    return [
        mp.log(table[q][i])
        + mp.log(table[qq][i])
        - mp.log(table[g][i])
        - mp.log(table[l][i])
        for i in range(len(table[1]))
    ]


def field_row(cfg, s_str, forms):
    s = mp.mpf(s_str)
    row = dict(s=s_str, pairs=[], moments={})
    for q, qq in cfg["pairs"]:
        g = gcd(q, qq)
        l = q * qq // g
        rq, rqq = q // g, qq // g
        t = mp.pi**2 / (4 * s * l * l)
        entry = dict(q=q, qq=qq)
        fields = {}
        for form in forms:
            tab = {m: masses(form, m * m * s, "coset") for m in {1, q, qq, g, l}}
            d = defect(tab, q, qq)
            fields[form] = d
            entry[form] = dict(
                class0=mp.nstr(d[0], 15),
                max=mp.nstr(max(d), 15),
                min=mp.nstr(min(d), 15),
                positive_classes=sum(1 for x in d if x > 0),
                sum=mp.nstr(mp.fsum(d), 20),
            )
            digits = twist_digits(form, t)
            if digits <= cfg["twist_digit_cap"]:
                ht = {
                    m: masses(form, m * m * t, "twist", digits)
                    for m in {1, rq, rqq, rq * rqq}
                }
                dh = defect(ht, rq, rqq)
                scale = max(abs(x) for x in d) + 1
                entry[form]["reflection_residual"] = mp.nstr(
                    max(abs(x - y) for x, y in zip(d, dh)) / scale, 3
                )
            else:
                entry[form]["reflection_residual"] = f"skipped ({digits} digits)"
        entry["sum_difference"] = mp.nstr(
            mp.fsum(fields[forms[0]]) - mp.fsum(fields[forms[1]]), 10
        )
        entry["multiset_equal"] = sorted(
            mp.nstr(x, 25) for x in fields[forms[0]]
        ) == sorted(mp.nstr(x, 25) for x in fields[forms[1]])
        row["pairs"].append(entry)
    for form in forms:
        th = masses(form, s, "coset")
        row["moments"][form] = [
            mp.nstr(mp.fsum(x**k for x in th), 25) for k in range(1, cfg["moments"] + 1)
        ]
    a, b = (row["moments"][f] for f in forms)
    row["moments_rel_difference"] = [
        mp.nstr(abs(mp.mpf(x) - mp.mpf(y)) / mp.mpf(x), 3) for x, y in zip(a, b)
    ]
    return row


def asymptotic_rows(cfg, forms, n4):
    """Small-scale law: the classes' summed defect separates the pair at
    fourth order in the twisted masses. Moments of order <= 3 agree, so

        sum_c D_c[E8^2] - sum_c D_c[D16+]
            ~ (2^16 / 4) (N4[E8^2] - N4[D16+]) exp(-8t),

    t the smallest reflected scale and N4 the root quadruples summing
    into 2L."""
    q, qq = cfg["asymptotic_pair"]
    g = gcd(q, qq)
    l = q * qq // g
    dn4 = n4[forms[0]] - n4[forms[1]]
    out = []
    for t_str in cfg["asymptotic_t"]:
        t = mp.mpf(t_str)
        s = mp.pi**2 / (4 * t * l * l)
        sums = []
        for form in forms:
            tab = {m: masses(form, m * m * s, "coset") for m in {1, q, qq, g, l}}
            sums.append(mp.fsum(defect(tab, q, qq)))
        observed = sums[0] - sums[1]
        predicted = mp.mpf(2) ** 16 / 4 * dn4 * mp.exp(-8 * t)
        out.append(
            dict(
                t=t_str,
                s=mp.nstr(s, 10),
                observed=mp.nstr(observed, 12),
                predicted=mp.nstr(predicted, 12),
                ratio=mp.nstr(observed / predicted, 12),
            )
        )
        print(f"t = {t_str} done", file=sys.stderr)
    return out


def sweep(args):
    cfg = SWEEP_CONFIG
    mp.mp.dps = cfg["dps"]
    forms = ("e8e8", "d16plus")
    n4 = {form: root_quadruples(form) for form in forms}
    rows = []
    for s_str in cfg["scales"]:
        rows.append(field_row(cfg, s_str, forms))
        print(f"s = {s_str} done", file=sys.stderr)
    record = dict(
        config=cfg,
        root_quadruples={f: str(v) for f, v in n4.items()},
        rows=rows,
        asymptotic=asymptotic_rows(cfg, forms, n4),
        mpmath=mp.__version__,
        numpy=np.__version__,
    )
    text = json.dumps(record, indent=2) + "\n"
    if args.write:
        path = DATA / "q3_field_e8e8_d16plus.json"
        path.write_text(text)
        print(f"wrote {path}", file=sys.stderr)
    print(text, end="")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(required=True)
    sub.add_parser("selftest").set_defaults(fn=selftest)
    p = sub.add_parser("sweep")
    p.add_argument("--write", action="store_true")
    p.set_defaults(fn=sweep)
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
