# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "mpmath==1.4.1",
# ]
# ///
"""Reconnaissance harness: higher-rank Q5 curvature profiles.

Evidence, not proof. This harness produces the numerical record the
README cites; nothing here is a theorem, and `lake build` remains the
only definition of proof. Conventions live in recon/README.md and are
enforced here as executable self-tests anchored to Lean theorems.

Conventions (summary):
  * Every Gram matrix is normalized to determinant 1 before profiling.
  * Scale variable u = log beta; the duality center is u = log pi.
  * H(u) = log Z(e^u);  H'(u) = -beta*<E>;  H''(u) = beta^2*Var(E) - beta*<E>.
  * Q5 (strict) at a form: H'' > 0 on the whole line. Equivalently the
    scale-free ratio  r(u) = beta*Var(E)/<E>  satisfies r > 1.
  * Dual form: Gram M^{-1} (det stays 1). Poisson summation gives
    Z_L(beta) = (pi/beta)^(n/2) * Z_{L*}(pi^2/beta), hence
    H_L''(u) = H_{L*}''(2 log pi - u): sweeping u >= log pi on both L
    and L* covers the whole line. Lean witness at rank one:
    theta_duality_real; higher rank is roadmap target 1.
  * Cutoff policy: box |x_i| <= R, checked empirically by a
    radius-stability comparison (R vs R+3) plus an ad hoc decay
    proxy. Neither is a tail bound; certified tails are roadmap
    target 5.

Self-test anchors, two classes:
  Lean-backed (rank one):
    * thetaDeriv_pi:          H'(log pi) = -1/4.
    * theta_logDeriv_dual:    H'(u) + H'(2 log pi - u) = -1/2.
    * hasDerivAt_thetaDeriv:  H'' is the derivative of H'.
  Higher-rank consistency checks (numerical only; no Lean witness yet,
  higher-rank duality being roadmap target 1):
    * hexagonal Poisson duality at beta = 2.
    * isodual center value H'(log pi) = -n/4.
"""

import argparse
import itertools
import json
import pathlib
import sys

import mpmath
from mpmath import exp, log, mp, mpf, nstr, pi, sqrt

# ---------------------------------------------------------------- forms

RAW_FORMS = {
    # Gram matrices BEFORE determinant normalization, exact rationals.
    "square2": [["1", "0"], ["0", "1"]],
    # (a^2 - a b + b^2)/3 -- the repo's hexagonal form (RankTwo.lean).
    # Raw determinant 1/12; its own reflection center is pi*sqrt(12).
    "hexagonal": [["1/3", "-1/6"], ["-1/6", "1/3"]],
}


def parse_gram(rows):
    n = len(rows)
    m = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            num = rows[i][j]
            if "/" in num:
                p, q = num.split("/")
                m[i, j] = mpf(p) / mpf(q)
            else:
                m[i, j] = mpf(num)
    return m


def det_normalize(m):
    """Scale M so that det M = 1 (mandatory before any profiling)."""
    n = m.rows
    d = mp.det(m)
    assert d > 0, "Gram matrix must be positive definite"
    return m / mp.root(d, n)


def dual(m):
    """Dual Gram: M^{-1}. Determinant-1 is preserved."""
    return m**-1


# ------------------------------------------------------- lattice sums


def box_qvalues(m, radius):
    """Q(x) = x^T M x for all x in the box |x_i| <= radius (0 included)."""
    n = m.rows
    qs = []
    for x in itertools.product(range(-radius, radius + 1), repeat=n):
        q = mpf(0)
        for i in range(n):
            for j in range(n):
                q += m[i, j] * x[i] * x[j]
        qs.append(q)
    return qs


def lambda1_sq(qs):
    """Shortest nonzero vector norm^2 = min of Q over the box minus 0."""
    return min(q for q in qs if q > 0)


def check_cutoff(m, radius, beta_min, dps):
    """Ad hoc decay proxy, NOT a tail bound (certified tails: target 5).

    Every dropped point has sup-norm > radius, hence
    Q >= mu * radius^2 with mu the least eigenvalue of M; this
    multiplies one such exponential by a crude polynomial allowance.
    The empirical check is `radius_stability` below.
    """
    n = m.rows
    mu = min(mp.eigsy(mp.matrix(m))[0])
    qmin = mu * radius**2
    allowance = (qmin**2 + 1) * (2 * radius + 3) ** n
    bound = allowance * exp(-beta_min * qmin)
    assert bound < mpf(10) ** (-(dps + 5)), (
        f"cutoff radius {radius} too small: dropped-term bound {nstr(bound, 5)}"
    )


def radius_stability(m, radius, u, dps):
    """Empirical cutoff check at the fattest tails swept (the duality
    center): H', H'', and the ratio must be radius-stable — the
    moments are more tail-sensitive than Z alone."""
    a = stats(box_qvalues(m, radius), u)
    b = stats(box_qvalues(m, radius + 3), u)
    for key in ("H1", "H2", "ratio"):
        rel = abs(a[key] - b[key]) / abs(b[key])
        assert rel < mpf(10) ** (-(dps - 8)), (
            f"radius {radius} not stable in {key}: shift {nstr(rel, 5)}"
        )


def stats(qs, u):
    """H'(u), H''(u), and the scale-free ratio at u = log beta."""
    beta = exp(u)
    Z = mpf(0)
    S1 = mpf(0)
    S2 = mpf(0)
    for q in qs:
        e = exp(-beta * q)
        Z += e
        S1 += q * e
        S2 += q * q * e
    E = S1 / Z
    var = S2 / Z - E * E
    H1 = -beta * E
    H2 = beta**2 * var - beta * E
    ratio = beta * var / E
    return {"beta": beta, "H1": H1, "H2": H2, "ratio": ratio}


# ------------------------------------------------------------ sweeps


def sweep_profile(qs, u0, du, npts):
    """Sweep u >= u0; track positivity of H'' and the minimum ratio."""
    min_ratio = None
    min_ratio_u = None
    min_H2 = None
    min_H2_u = None
    positive = True
    center = stats(qs, u0)
    for k in range(npts):
        u = u0 + k * du
        st = stats(qs, u)
        if st["H2"] <= 0:
            positive = False
        if min_H2 is None or st["H2"] < min_H2:
            min_H2, min_H2_u = st["H2"], u
        if min_ratio is None or st["ratio"] < min_ratio:
            min_ratio, min_ratio_u = st["ratio"], u
    return {
        "H2_positive_on_grid": positive,
        "center": center,
        "min_H2_on_grid": min_H2,
        "min_H2_at_u_minus_logpi": min_H2_u - u0,
        "min_ratio_on_grid": min_ratio,
        "min_ratio_at_u_minus_logpi": min_ratio_u - u0,
    }


def s(x, digits=30):
    return nstr(x, digits)


def run_sweep(name, radius, u_span, du, dps, outdir):
    mp.dps = dps
    m = det_normalize(parse_gram(RAW_FORMS[name]))
    n = m.rows
    md = dual(m)
    u0 = log(pi)
    npts = int(u_span / du) + 1
    check_cutoff(m, radius, exp(u0), dps)
    check_cutoff(md, radius, exp(u0), dps)
    radius_stability(m, radius, u0, dps)
    radius_stability(md, radius, u0, dps)

    qs = box_qvalues(m, radius)
    qsd = box_qvalues(md, radius)
    l1 = lambda1_sq(qs)
    l1d = lambda1_sq(qsd)

    prof = sweep_profile(qs, u0, mpf(du), npts)
    profd = sweep_profile(qsd, u0, mpf(du), npts)

    result = {
        "form": name,
        "rank": n,
        "gram_normalized": [[s(m[i, j]) for j in range(n)] for i in range(n)],
        "det_check": s(mp.det(m)),
        "lambda1_sq": s(l1),
        "dual_lambda1_sq": s(l1d),
        "lambda1_product": s(sqrt(l1 * l1d)),
        "grid": {"u0": "log(pi)", "span": u_span, "step": du, "points": npts},
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "cutoff_radius": radius,
        "L": {k: (s(v) if isinstance(v, mpf) else
                  ({kk: s(vv) for kk, vv in v.items()} if isinstance(v, dict) else v))
              for k, v in prof.items()},
        "L_dual": {k: (s(v) if isinstance(v, mpf) else
                       ({kk: s(vv) for kk, vv in v.items()} if isinstance(v, dict) else v))
                   for k, v in profd.items()},
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / f"{name}.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"[{name}] rank {n}, lambda1^2 = {s(l1, 10)}, "
          f"lambda1(L)*lambda1(L*) = {s(sqrt(l1 * l1d), 10)}")
    for tag, p in (("L", prof), ("L*", profd)):
        print(f"  {tag}: H'' > 0 on grid: {p['H2_positive_on_grid']}; "
              f"H''(log pi) = {s(p['center']['H2'], 10)}; "
              f"sampled min ratio = {s(p['min_ratio_on_grid'], 10)} "
              f"at u - log pi = {s(p['min_ratio_at_u_minus_logpi'], 6)}")
    print(f"  -> {out}")
    return result


# ---------------------------------------------------------- selftest


def selftest(dps):
    mp.dps = dps
    tol = mpf(10) ** (-(dps - 12))
    failures = []

    def check(label, residual, tolerance):
        ok = abs(residual) < tolerance
        print(f"  {'PASS' if ok else 'FAIL'}  {label}: residual {s(residual, 8)}")
        if not ok:
            failures.append(label)

    print("selftest: [lean] = Lean-backed anchor, [num] = numerical consistency check")
    one = det_normalize(parse_gram([["1"]]))
    qs1 = box_qvalues(one, 60)
    u0 = log(pi)

    # thetaDeriv_pi: H'(log pi) = -1/4 at rank one.
    check("[lean] thetaDeriv_pi (rank one, H'(log pi) = -1/4)",
          stats(qs1, u0)["H1"] + mpf(1) / 4, tol)

    # theta_logDeriv_dual: H'(u) + H'(2 log pi - u) = -1/2 at rank one.
    u = u0 + mpf("0.7")
    check("[lean] theta_logDeriv_dual (H'(u) + H'(2 log pi - u) = -1/2)",
          stats(qs1, u)["H1"] + stats(qs1, 2 * u0 - u)["H1"] + mpf(1) / 2, tol)

    # Finite-difference consistency of H'' against H'.
    h = mpf(10) ** (-10)
    ufd = u0 + mpf("0.3")
    fd = (stats(qs1, ufd + h)["H1"] - stats(qs1, ufd - h)["H1"]) / (2 * h)
    check("[lean] hasDerivAt_thetaDeriv (H'' = d/du H', finite diff)",
          stats(qs1, ufd)["H2"] - fd, mpf(10) ** (-(dps - 35)))

    # Hexagonal, determinant-normalized: Poisson duality at beta = 2.
    hexm = det_normalize(parse_gram(RAW_FORMS["hexagonal"]))
    hexd = dual(hexm)
    qsh = box_qvalues(hexm, 25)
    qshd = box_qvalues(hexd, 25)
    beta = mpf(2)
    zl = sum(exp(-beta * q) for q in qsh)
    zr = (pi / beta) * sum(exp(-(pi**2 / beta) * q) for q in qshd)
    check("[num]  Poisson duality, hexagonal (Z_L(2) = (pi/2) Z_{L*}(pi^2/2))",
          zl - zr, tol)

    # Isodual center anchor: hexagonal H'(log pi) = -2/4.
    check("[num]  isodual center (hexagonal, H'(log pi) = -1/2)",
          stats(qsh, u0)["H1"] + mpf(1) / 2, tol)

    if failures:
        print(f"selftest: {len(failures)} FAILURE(S)")
        sys.exit(1)
    print("selftest: all anchors reproduced")


# --------------------------------------------------------------- cli


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=["selftest", "sweep", "all"])
    ap.add_argument("--form", choices=sorted(RAW_FORMS), default=None)
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--radius", type=int, default=14)
    ap.add_argument("--span", type=float, default=4.0)
    ap.add_argument("--step", type=float, default=0.01)
    args = ap.parse_args()

    outdir = pathlib.Path(__file__).parent / "data"
    if args.command in ("selftest", "all"):
        selftest(args.dps)
    if args.command == "sweep":
        forms = [args.form] if args.form else sorted(RAW_FORMS)
        for f in forms:
            run_sweep(f, args.radius, args.span, args.step, args.dps, outdir)
    if args.command == "all":
        for f in sorted(RAW_FORMS):
            run_sweep(f, args.radius, args.span, args.step, args.dps, outdir)


if __name__ == "__main__":
    main()
