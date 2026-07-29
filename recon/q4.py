# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "mpmath==1.4.1",
# ]
# ///
"""Q4 phase geometry: CND and deficit-PSD transitions of the prime
pairing, as functions of the scale.

Evidence, not proof. Companion to harness.py (Q5 profiles); shares
its conventions and data policy (recon/README.md).

Objects, with the repo's normalizations:
  * theta(a) = sum_{k in Z} exp(-a k^2);  F(m) := log theta(m^2 s).
  * The prime pairing <p,q> = F(1) + F(pq) - F(p) - F(q) for
    distinct primes (minus the defect), zero on the diagonal;
    M(s) is its matrix on a finite prime set P.
  * The saturation deficit B(s): F(p) + F(q) - F(pq) off the
    diagonal, F(1) on it.

Orientation conventions (the ones a reviewer once had to correct):
  * Q4-CND is controlled by the LARGEST eigenvalue of M restricted
    to the zero-sum subspace: CND holds iff it is <= 0.
  * Q4-PSD is controlled by the ordinary SMALLEST eigenvalue of B:
    PSD holds iff it is >= 0.

The sweep tracks both statistics on a log-spaced grid, counts sign
changes (the intervality probe: falsify before proving), and
bisects each detected crossing.

Self-test anchors, two classes:
  Lean-backed:
    * pairing_pos:            off-diagonal entries of M are > 0.
    * pairing_lt_base:        <p,q> < log theta(s) (B off-diag > 0).
    * pairing_cnd_large:      for s >= 1, largest zero-sum-restricted
                              eigenvalue of M is <= 0.
    * quadFormOn_pairing_eq:  the exact zero-sum identity -- the
                              pairing quadratic form equals the
                              product-kernel form minus the diagonal
                              of Q5 curvatures.
  Numerical consistency:
    * tendsto_exp_mul_pairing (loose): at small s, the normalized
      pairing e^sigma * <p,q> / 2 with sigma = pi^2/(s p^2 q^2) is
      near 1 (the Lean theorem is the limit; the rate is not one).
"""

import argparse
import json
import pathlib
import sys

import mpmath
from mpmath import exp, log, mp, mpf, nstr, pi

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def theta(alpha, dps):
    """theta(alpha) = 1 + 2 sum_{k>=1} exp(-alpha k^2), truncated at
    the energy cutoff E = (dps+15) ln 10 (same policy as harness)."""
    energy = (mpf(dps) + 15) * mp.log(10)
    kmax = int(mp.ceil(mp.sqrt(energy / alpha)))
    return 1 + 2 * sum(exp(-alpha * k * k) for k in range(1, kmax + 1))


def bigF(m, s, dps):
    return log(theta(mpf(m) ** 2 * s, dps))


def pairing(p, q, s, dps):
    if p == q:
        return mpf(0)
    return (bigF(1, s, dps) + bigF(p * q, s, dps)
            - bigF(p, s, dps) - bigF(q, s, dps))


def pairing_matrix(ps, s, dps):
    n = len(ps)
    m = mp.matrix(n, n)
    for i in range(n):
        for j in range(i + 1, n):
            v = pairing(ps[i], ps[j], s, dps)
            m[i, j] = v
            m[j, i] = v
    return m


def deficit_matrix(ps, s, dps):
    n = len(ps)
    f1 = bigF(1, s, dps)
    m = mp.matrix(n, n)
    for i in range(n):
        m[i, i] = f1
        for j in range(i + 1, n):
            v = (bigF(ps[i], s, dps) + bigF(ps[j], s, dps)
                 - bigF(ps[i] * ps[j], s, dps))
            m[i, j] = v
            m[j, i] = v
    return m


def zero_sum_basis(n):
    """Orthonormal basis of the zero-sum subspace (Helmert)."""
    u = mp.matrix(n, n - 1)
    for j in range(1, n):
        norm = mp.sqrt(mpf(j * (j + 1)))
        for i in range(j):
            u[i, j - 1] = 1 / norm
        u[j, j - 1] = -mpf(j) / norm
    return u


def cnd_stat(ps, s, dps):
    """Largest eigenvalue of M restricted to the zero-sum subspace.
    CND holds iff this is <= 0."""
    m = pairing_matrix(ps, s, dps)
    u = zero_sum_basis(len(ps))
    a = u.T * m * u
    return max(mp.eigsy(a)[0])


def psd_stat(ps, s, dps):
    """Smallest ordinary eigenvalue of the deficit B. PSD holds iff
    this is >= 0."""
    return min(mp.eigsy(deficit_matrix(ps, s, dps))[0])


def bisect_crossing(stat, ps, lo, hi, dps, iters=40):
    """Refine a sign change of stat between lo and hi."""
    flo = stat(ps, lo, dps)
    for _ in range(iters):
        mid = mp.sqrt(lo * hi)
        fmid = stat(ps, mid, dps)
        if (flo > 0) == (fmid > 0):
            lo, flo = mid, fmid
        else:
            hi = mid
    return mp.sqrt(lo * hi)


def s_grid(lo, hi, npts):
    llo, lhi = log(mpf(lo)), log(mpf(hi))
    return [exp(llo + (lhi - llo) * k / (npts - 1)) for k in range(npts)]


def s(x, digits=30):
    return nstr(x, digits)


def sweep_set(k, grid_lo, grid_hi, npts, dps, outdir):
    mp.dps = dps
    ps = PRIMES[:k]
    grid = s_grid(grid_lo, grid_hi, npts)
    rows = {}
    for name, stat in (("cnd", cnd_stat), ("psd", psd_stat)):
        vals = [stat(ps, x, dps) for x in grid]
        crossings = []
        for i in range(1, len(vals)):
            if (vals[i - 1] > 0) != (vals[i] > 0):
                crossings.append(
                    bisect_crossing(stat, ps, grid[i - 1], grid[i], dps))
        # CND valid where stat <= 0; PSD valid where stat >= 0.
        ok_at_top = (vals[-1] <= 0) if name == "cnd" else (vals[-1] >= 0)
        rows[name] = {
            "sign_changes": len(crossings),
            "crossings": [s(c, 12) for c in crossings],
            "valid_at_grid_top": bool(ok_at_top),
            "stat_at_grid_top": s(vals[-1], 12),
        }
        print(f"  {k} primes, {name}: sign changes {len(crossings)}, "
              f"crossings {[s(c, 6) for c in crossings]}, "
              f"valid at s = {grid_hi}: {ok_at_top}")
    result = {
        "primes": ps,
        "grid": {"lo": grid_lo, "hi": grid_hi, "points": npts,
                 "spacing": "log"},
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "cnd_statistic": "largest zero-sum-restricted eigenvalue of M"
                         " (CND iff <= 0)",
        "psd_statistic": "smallest eigenvalue of B (PSD iff >= 0)",
        **rows,
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / f"q4_sweep_{k}primes.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"  -> {out}")


def witness(dps, outdir):
    """The five-prime s = 0.12 witness: CND holds, deficit-PSD fails
    -- the numerical separation of Q4's two clauses."""
    mp.dps = dps
    ps = PRIMES[:5]
    x = mpf("0.12")
    c = cnd_stat(ps, x, dps)
    p = psd_stat(ps, x, dps)
    result = {
        "primes": ps,
        "s": "0.12",
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "cnd_stat": s(c),
        "psd_stat": s(p),
        "cnd_holds": bool(c <= 0),
        "psd_holds": bool(p >= 0),
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / "q4_witness.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"[witness] 5 primes at s = 0.12: CND stat {s(c, 8)} "
          f"(holds: {c <= 0}), PSD stat {s(p, 8)} (holds: {p >= 0})")
    print(f"  -> {out}")


def selftest(dps):
    mp.dps = dps
    tol = mpf(10) ** (-(dps - 12))
    failures = []

    def check(label, ok, detail):
        print(f"  {'PASS' if ok else 'FAIL'}  {label}: {detail}")
        if not ok:
            failures.append(label)

    print("selftest: [lean] = Lean-backed anchor, "
          "[num] = numerical consistency check")
    ps = PRIMES[:4]
    x = mpf("0.3")

    m = pairing_matrix(ps, x, dps)
    off = [m[i, j] for i in range(4) for j in range(4) if i != j]
    check("[lean] pairing_pos (off-diagonal entries > 0)",
          all(v > 0 for v in off), f"min {s(min(off), 8)}")

    base = bigF(1, x, dps)
    check("[lean] pairing_lt_base (<p,q> < log theta(s))",
          all(v < base for v in off),
          f"max gap {s(base - max(off), 8)}")

    ok = True
    worst = mpf("-inf")
    for sv in ("1", "1.5", "3"):
        c = cnd_stat(PRIMES[:5], mpf(sv), dps)
        worst = max(worst, c)
        ok = ok and c <= 0
    check("[lean] pairing_cnd_large (restricted lam_max <= 0, s >= 1)",
          ok, f"largest over s in {{1, 1.5, 3}}: {s(worst, 8)}")

    # quadFormOn_pairing_eq: exact zero-sum identity on {2,3,5,7}.
    c = [mpf(1), mpf(2), mpf(-1), mpf(-2)]
    lhs = mpf(0)
    for i in range(4):
        for j in range(4):
            lhs += c[i] * c[j] * m[i, j]
    rhs = mpf(0)
    for i in range(4):
        for j in range(4):
            rhs += c[i] * c[j] * log(theta((mpf(ps[i]) * ps[j]) ** 2 * x, dps))
    for i in range(4):
        rhs -= c[i] ** 2 * (log(theta(x, dps))
                            + log(theta(mpf(ps[i]) ** 4 * x, dps))
                            - 2 * log(theta(mpf(ps[i]) ** 2 * x, dps)))
    check("[lean] quadFormOn_pairing_eq (exact zero-sum identity)",
          abs(lhs - rhs) < tol, f"residual {s(lhs - rhs, 8)}")

    sv = mpf("0.02")
    sigma = pi**2 / (sv * 36)
    norm = exp(sigma) * pairing(2, 3, sv, dps) / 2
    check("[num]  tendsto_exp_mul_pairing (loose, s = 0.02)",
          mpf("0.5") < norm < mpf("1.5"), f"normalized value {s(norm, 8)}")

    if failures:
        print(f"selftest: {len(failures)} FAILURE(S)")
        sys.exit(1)
    print("selftest: all anchors reproduced")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=["selftest", "sweep", "witness", "all"])
    ap.add_argument("--kprimes", type=int, default=None)
    ap.add_argument("--lo", default="0.02")
    ap.add_argument("--hi", default="1.5")
    ap.add_argument("--points", type=int, default=160)
    ap.add_argument("--dps", type=int, default=30)
    args = ap.parse_args()

    outdir = pathlib.Path(__file__).parent / "data"
    if args.command in ("selftest", "all"):
        selftest(args.dps)
    if args.command in ("sweep", "all"):
        ks = [args.kprimes] if args.kprimes else [3, 5, 7, 10, 15]
        for k in ks:
            if k < 2 or k > len(PRIMES):
                ap.error(f"--kprimes must be in [2, {len(PRIMES)}]; "
                         f"extend PRIMES for larger sets")
            print(f"[q4 sweep] first {k} primes, "
                  f"s in [{args.lo}, {args.hi}], {args.points} points")
            sweep_set(k, args.lo, args.hi, args.points, args.dps, outdir)
    if args.command in ("witness", "all"):
        witness(args.dps, outdir)


if __name__ == "__main__":
    main()
