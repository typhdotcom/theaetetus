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
    Rank-two caveat: with J = [[0,-1],[1,0]] in GL_2(Z), every
    det-1 symmetric 2x2 matrix satisfies J^T M J = M^{-1} -- every
    binary form here is integrally isodual, so L/L* agreement in
    rank two checks matrix inversion and basis invariance only.
    Genuinely distinct dual pairs first appear at rank 3 (FCC/BCC).
  * Cutoff policy: lattice points are enumerated over the axis-aligned
    bounding box of the energy ellipsoid Q <= E -- the "box energy" E
    is set by the working precision and the smallest coupling in use,
    and |x_i| <= sqrt(E * (M^{-1})_ii). The box adapts per direction,
    so degenerating forms stay cheap. Checked empirically by an
    energy-stability comparison (E vs 1.5E). Not a tail bound;
    certified tails are roadmap target 5.

Self-test anchors, two classes:
  Lean-backed (rank one):
    * thetaDeriv_pi:          H'(log pi) = -1/4.
    * theta_logDeriv_dual:    H'(u) + H'(2 log pi - u) = -1/2.
    * hasDerivAt_thetaDeriv:  H'' is the derivative of H'.
  Higher-rank consistency checks (numerical only; no Lean witness yet,
  higher-rank duality being roadmap target 1):
    * hexagonal Poisson duality at beta = 2 (rank 2).
    * FCC/BCC Poisson duality at beta = 2 (rank 3).
    * self-dual center value H'(log pi) = -n/4 (hexagonal, cubic).
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
    # Rank 3: cubic Z^3 (self-dual) and FCC, whose dual is BCC --
    # the first genuinely distinct dual pair in the program.
    "cubic3": [["1", "0", "0"], ["0", "1", "0"], ["0", "0", "1"]],
    "fcc": [["2", "1", "1"], ["1", "2", "1"], ["1", "1", "2"]],
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


def mat_eye(n):
    m = mp.matrix(n, n)
    for i in range(n):
        m[i, i] = mpf(1)
    return m


def mat_diag(vals):
    n = len(vals)
    m = mp.matrix(n, n)
    for i in range(n):
        m[i, i] = vals[i]
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


def box_energy(dps, beta_min):
    """Energy cutoff E: dropped points have Boltzmann weight below
    exp(-beta_min * E), far under working precision."""
    return (mpf(dps) + 15) * mp.log(10) / beta_min


def box_radii(m, energy):
    """Axis-aligned bounding box of the ellipsoid Q <= energy:
    |x_i| <= sqrt(energy * (M^{-1})_ii). Adapts per direction, so
    degenerating forms stay cheap."""
    minv = m**-1
    return [int(mp.ceil(sqrt(energy * minv[i, i]))) for i in range(m.rows)]


def box_qvalues(m, radii):
    """Q(x) = x^T M x for all x in the box |x_i| <= radii[i]."""
    n = m.rows
    qs = []
    ranges = [range(-r, r + 1) for r in radii]
    for x in itertools.product(*ranges):
        q = mpf(0)
        for i in range(n):
            for j in range(n):
                q += m[i, j] * x[i] * x[j]
        qs.append(q)
    return qs


def qvalues_at(m, dps, beta_min):
    """Q-values over the ellipsoid bounding box sized for beta_min."""
    return box_qvalues(m, box_radii(m, box_energy(dps, beta_min)))


def lambda1_sq(qs):
    """Shortest nonzero vector norm^2 = min of Q over the box minus 0."""
    return min(q for q in qs if q > 0)


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


def energy_stability(m, u, dps, beta_min):
    """Empirical cutoff check at the smallest coupling in use: H',
    H'', and the ratio must agree between boxes for E and 1.5E --
    the moments are more tail-sensitive than Z alone."""
    e0 = box_energy(dps, beta_min)
    a = stats(box_qvalues(m, box_radii(m, e0)), u)
    b = stats(box_qvalues(m, box_radii(m, mpf("1.5") * e0)), u)
    for key in ("H1", "H2", "ratio"):
        rel = abs(a[key] - b[key]) / abs(b[key])
        assert rel < mpf(10) ** (-(dps - 8)), (
            f"box energy not stable in {key}: shift {nstr(rel, 5)}"
        )


# ----------------------------------------------------------- families

FAMILY_NAMES = [
    "unit_circle_arc",
    "shear_half",
    "rank3_baselines",
    "cubic_to_fcc",
    "fcc_squash",
]


def gram_of_tau(x, y):
    """Det-1 Gram of the binary form with modular parameter tau = x+iy:
    Q(m,n) = |m + n*tau|^2 / y. Covers every det-1 positive binary
    form up to equivalence."""
    m = mp.matrix(2, 2)
    m[0, 0] = 1 / y
    m[0, 1] = x / y
    m[1, 0] = x / y
    m[1, 1] = (x * x + y * y) / y
    return m


def build_family(name):
    """Members as (label, raw Gram). Endpoint members coincide with
    committed baselines (built-in cross-checks). The unit-circle arc
    is distinguished in tau-space, not by isoduality: in det-1 rank
    two every form is integrally isodual (module docstring)."""
    if name == "unit_circle_arc":
        out = []
        for deg in (60, 65, 70, 75, 80, 85, 90):
            phi = mpf(deg) * pi / 180
            out.append((f"phi{deg}", gram_of_tau(mp.cos(phi), mp.sin(phi))))
        return out
    if name == "shear_half":
        ys = [
            "0.86602540378443864676",
            "0.6",
            "0.45",
            "0.35",
            "0.25",
            "0.18",
            "0.12",
            "0.08",
            "0.05",
        ]
        return [(f"y{v}", gram_of_tau(mpf("0.5"), mpf(v))) for v in ys]
    if name == "rank3_baselines":
        return [
            ("cubic3", parse_gram(RAW_FORMS["cubic3"])),
            ("fcc", parse_gram(RAW_FORMS["fcc"])),
        ]
    if name == "cubic_to_fcc":
        fcc = det_normalize(parse_gram(RAW_FORMS["fcc"]))
        eye = mat_eye(3)
        out = []
        for k in range(7):
            t = mpf(k) / 6
            out.append((f"t{k}of6", eye * (1 - t) + fcc * t))
        return out
    if name == "fcc_squash":
        fcc = parse_gram(RAW_FORMS["fcc"])
        out = []
        for v in ("1", "0.7", "0.5", "0.35", "0.25", "0.15", "0.10", "0.07"):
            y = mpf(v)
            d = mat_diag([mpf(1), mpf(1), y])
            out.append((f"y{v}", d * fcc * d))
        return out
    raise ValueError(f"unknown family {name}")


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


def gram_strings(m):
    return [[s(m[i, j]) for j in range(m.rows)] for i in range(m.rows)]


def profile_pair(m, dps, u0, du, npts):
    """Q-values and profiles for a normalized form and its dual,
    with the stability checks run for both."""
    md = dual(m)
    beta_min = exp(u0)
    energy_stability(m, u0, dps, beta_min)
    energy_stability(md, u0, dps, beta_min)
    qs = qvalues_at(m, dps, beta_min)
    qsd = qvalues_at(md, dps, beta_min)
    return (qs, qsd, sweep_profile(qs, u0, du, npts), sweep_profile(qsd, u0, du, npts))


def wrap_profile(p):
    return {
        k: (
            s(v)
            if isinstance(v, mpf)
            else ({kk: s(vv) for kk, vv in v.items()} if isinstance(v, dict) else v)
        )
        for k, v in p.items()
    }


def run_sweep(name, u_span, du, dps, outdir):
    mp.dps = dps
    m = det_normalize(parse_gram(RAW_FORMS[name]))
    n = m.rows
    u0 = log(pi)
    npts = int(u_span / du) + 1
    qs, qsd, prof, profd = profile_pair(m, dps, u0, mpf(du), npts)
    l1 = lambda1_sq(qs)
    l1d = lambda1_sq(qsd)
    result = {
        "form": name,
        "rank": n,
        "gram_normalized": gram_strings(m),
        "det_check": s(mp.det(m)),
        "lambda1_sq": s(l1),
        "dual_lambda1_sq": s(l1d),
        "lambda1_product": s(sqrt(l1 * l1d)),
        "grid": {"u0": "log(pi)", "span": u_span, "step": du, "points": npts},
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "box_energy": s(box_energy(dps, exp(u0))),
        "box_radii": {
            "L": box_radii(m, box_energy(dps, exp(u0))),
            "L_dual": box_radii(dual(m), box_energy(dps, exp(u0))),
        },
        "L": wrap_profile(prof),
        "L_dual": wrap_profile(profd),
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / f"{name}.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(
        f"[{name}] rank {n}, lambda1^2 = {s(l1, 10)}, "
        f"lambda1(L)*lambda1(L*) = {s(sqrt(l1 * l1d), 10)}"
    )
    for tag, p in (("L", prof), ("L*", profd)):
        print(
            f"  {tag}: H'' > 0 on grid: {p['H2_positive_on_grid']}; "
            f"H''(log pi) = {s(p['center']['H2'], 10)}; "
            f"sampled min ratio = {s(p['min_ratio_on_grid'], 10)} "
            f"at u - log pi = {s(p['min_ratio_at_u_minus_logpi'], 6)}"
        )
    print(f"  -> {out}")


def run_family(name, u_span, du, dps, outdir):
    mp.dps = dps
    u0 = log(pi)
    npts = int(u_span / du) + 1
    rows = []
    print(f"[family {name}] dps={dps}, grid step {du}, span {u_span}")
    for label, mraw in build_family(name):
        m = det_normalize(mraw)
        qs, qsd, prof, profd = profile_pair(m, dps, u0, mpf(du), npts)
        l1 = lambda1_sq(qs)
        l1d = lambda1_sq(qsd)
        if prof["min_ratio_on_grid"] <= profd["min_ratio_on_grid"]:
            side, best = "L", prof
        else:
            side, best = "L*", profd
        rows.append(
            {
                "label": label,
                "gram_normalized": gram_strings(m),
                "lambda1_product": s(sqrt(l1 * l1d)),
                "box_radii": {
                    "L": box_radii(m, box_energy(dps, exp(u0))),
                    "L_dual": box_radii(dual(m), box_energy(dps, exp(u0))),
                },
                "H2_positive_on_grid_both": bool(
                    prof["H2_positive_on_grid"] and profd["H2_positive_on_grid"]
                ),
                "sampled_min_ratio": s(best["min_ratio_on_grid"]),
                "min_side": side,
                "min_at_u_minus_logpi": s(best["min_ratio_at_u_minus_logpi"]),
            }
        )
        print(
            f"  {label:>10}: l1*l1d = {s(sqrt(l1 * l1d), 8):>10}, "
            f"min r = {s(best['min_ratio_on_grid'], 8):>10} "
            f"({side} at u-logpi = {s(best['min_ratio_at_u_minus_logpi'], 4)}), "
            f"H''>0 on grid: {rows[-1]['H2_positive_on_grid_both']}"
        )
    result = {
        "family": name,
        "grid": {"u0": "log(pi)", "span": u_span, "step": du, "points": npts},
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "members": rows,
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / f"family_{name}.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"  -> {out}")


def run_finescan(family, member, window, step, dps, outdir):
    """Fine grid around the duality center for one family member,
    committed as its own dataset. Same checks as every sweep."""
    mp.dps = dps
    u0 = log(pi)
    members = dict(build_family(family))
    m = det_normalize(members[member])
    md = dual(m)
    beta_min = exp(u0)
    energy_stability(m, u0, dps, beta_min)
    energy_stability(md, u0, dps, beta_min)
    w = mpf(window)
    du = mpf(step)
    npts = int(w / du) + 1
    print(f"[finescan {family}/{member}] window {window}, step {step}, dps {dps}")
    sides = {}
    for tag, mm in (("L", m), ("L_dual", md)):
        qs = qvalues_at(mm, dps, beta_min)
        best_v = None
        best_u = None
        for k in range(npts):
            u = u0 + k * du
            st = stats(qs, u)
            if best_v is None or st["ratio"] < best_v:
                best_v, best_u = st["ratio"], u - u0
        sides[tag] = {"sampled_min_ratio": s(best_v), "at_u_minus_logpi": s(best_u)}
        print(
            f"  {tag}: sampled min ratio {s(best_v, 12)} at u - log pi = {s(best_u, 6)}"
        )
    result = {
        "family": family,
        "member": member,
        "gram_normalized": gram_strings(m),
        "window": window,
        "step": step,
        "precision_dps": dps,
        "mpmath_version": mpmath.__version__,
        "box_energy": s(box_energy(dps, beta_min)),
        "box_radii": {
            "L": box_radii(m, box_energy(dps, beta_min)),
            "L_dual": box_radii(md, box_energy(dps, beta_min)),
        },
        **sides,
    }
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / f"finescan_{family}_{member}.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"  -> {out}")


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
    u0 = log(pi)
    one = det_normalize(parse_gram([["1"]]))

    # thetaDeriv_pi: H'(log pi) = -1/4 at rank one.
    qs1 = qvalues_at(one, dps, exp(u0))
    check(
        "[lean] thetaDeriv_pi (rank one, H'(log pi) = -1/4)",
        stats(qs1, u0)["H1"] + mpf(1) / 4,
        tol,
    )

    # theta_logDeriv_dual: H'(u) + H'(2 log pi - u) = -1/2 at rank one.
    u = u0 + mpf("0.7")
    qs1w = qvalues_at(one, dps, exp(2 * u0 - u))
    check(
        "[lean] theta_logDeriv_dual (H'(u) + H'(2 log pi - u) = -1/2)",
        stats(qs1w, u)["H1"] + stats(qs1w, 2 * u0 - u)["H1"] + mpf(1) / 2,
        tol,
    )

    # Finite-difference consistency of H'' against H'.
    h = mpf(10) ** (-10)
    ufd = u0 + mpf("0.3")
    fd = (stats(qs1, ufd + h)["H1"] - stats(qs1, ufd - h)["H1"]) / (2 * h)
    check(
        "[lean] hasDerivAt_thetaDeriv (H'' = d/du H', finite diff)",
        stats(qs1, ufd)["H2"] - fd,
        mpf(10) ** (-(dps - 35)),
    )

    # Poisson duality checks at beta = 2 (each coupling boxed for itself).
    def poisson_residual(mn):
        md = dual(mn)
        beta = mpf(2)
        n = mn.rows
        zl = sum(exp(-beta * q) for q in qvalues_at(mn, dps, beta))
        zr = (pi / beta) ** (mpf(n) / 2) * sum(
            exp(-(pi**2 / beta) * q) for q in qvalues_at(md, dps, pi**2 / beta)
        )
        return zl - zr

    hexm = det_normalize(parse_gram(RAW_FORMS["hexagonal"]))
    check(
        "[num]  Poisson duality, hexagonal (rank 2, beta = 2)",
        poisson_residual(hexm),
        tol,
    )
    fccm = det_normalize(parse_gram(RAW_FORMS["fcc"]))
    check(
        "[num]  Poisson duality, FCC/BCC (rank 3, beta = 2)",
        poisson_residual(fccm),
        tol,
    )

    # Self-dual center values H'(log pi) = -n/4.
    qsh = qvalues_at(hexm, dps, exp(u0))
    check(
        "[num]  self-dual center (hexagonal, H'(log pi) = -1/2)",
        stats(qsh, u0)["H1"] + mpf(1) / 2,
        tol,
    )
    cub = det_normalize(parse_gram(RAW_FORMS["cubic3"]))
    qsc = qvalues_at(cub, dps, exp(u0))
    check(
        "[num]  self-dual center (cubic, H'(log pi) = -3/4)",
        stats(qsc, u0)["H1"] + mpf(3) / 4,
        tol,
    )

    if failures:
        print(f"selftest: {len(failures)} FAILURE(S)")
        sys.exit(1)
    print("selftest: all anchors reproduced")


# --------------------------------------------------------------- cli


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "command", choices=["selftest", "sweep", "family", "finescan", "all"]
    )
    ap.add_argument("--form", choices=sorted(RAW_FORMS), default=None)
    ap.add_argument("--family", choices=FAMILY_NAMES, default=None)
    ap.add_argument("--member", default=None)
    ap.add_argument("--window", default="0.3")
    ap.add_argument("--finestep", default="0.0005")
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--span", type=float, default=4.0)
    ap.add_argument("--step", type=float, default=0.01)
    args = ap.parse_args()

    outdir = pathlib.Path(__file__).parent / "data"
    if args.command in ("selftest", "all"):
        selftest(args.dps)
    if args.command == "sweep":
        forms = [args.form] if args.form else ["hexagonal", "square2"]
        for f in forms:
            run_sweep(f, args.span, args.step, args.dps, outdir)
    if args.command == "family":
        fams = [args.family] if args.family else FAMILY_NAMES
        for f in fams:
            run_family(f, args.span, 0.02, 30, outdir)
    if args.command == "finescan":
        assert args.family and args.member, "finescan needs --family and --member"
        run_finescan(
            args.family, args.member, args.window, args.finestep, args.dps, outdir
        )
    if args.command == "all":
        for f in ("hexagonal", "square2"):
            run_sweep(f, args.span, args.step, args.dps, outdir)
        for f in FAMILY_NAMES:
            run_family(f, args.span, 0.02, 30, outdir)
        run_finescan("shear_half", "y0.05", "0.3", "0.0005", 30, outdir)
        run_finescan("fcc_squash", "y0.10", "1.4", "0.002", 30, outdir)
        run_finescan("fcc_squash", "y0.07", "1.4", "0.002", 30, outdir)


if __name__ == "__main__":
    main()
