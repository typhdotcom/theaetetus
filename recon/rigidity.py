# /// script
# requires-python = ">=3.12,<3.13"
# dependencies = [
#     "python-flint==0.9.0",
# ]
# ///
"""Reconnaissance: the two-grid rigidity campaign (falsify-first).

Evidence, not proof. `lake build` remains the only definition of done.

The question. For a positive-definite Gram form `M`, coprime `a, b`
and scale `s`, the Gram defect

    D_s(a, b) = log Z(a^2 s) + log Z(b^2 s)
                - log Z(s) - log Z((ab)^2 s),      Z(t) = gramTheta(M, t)

is nonpositive (Lean: `gramDefect_nonpos`) and vanishes exactly when
the two-grid reflection criterion holds (Lean:
`gramDefect_eq_zero_iff_twoGridReflection`). The open roadmap item is
that it never vanishes for coprime `a, b > 1` in positive rank. This
script searches the sampled families for a counterexample and, failing
that, measures how far from zero the obstruction stays.

Two statistics per point:

  * the scalar slack `-D_s(a,b) >= 0`, from four lattice sums;
  * the *two-grid residual*, the largest failure of the reflection
    identity itself over the sampled classes,

        R = max over r in (Z/b)^d, c in (Z/a)^d, e in (Z/2)^d of
            | P(v_r + v_c)(e) - P(v_r - v_c)(e) |,
      reported as an Arb interval-maximum fold, alongside one class
      whose own residual is certified positive (a witness, not a
      certified argmax),
        P(z)(e) = gramMass(M, 2*beta, (z + e)/2),  beta = a^2 b^2 s,
        v_r = r/b,  v_c = c/a.

    Zero defect requires *every* residual to vanish, so a small scalar
    slack alone is not evidence of geometric saturation.

What "certified" means here. Nothing in this directory is a proof, and
the roadmap's formal chain is Lean's alone. Inside that limit the
arithmetic is rigorous rather than heuristic:

  * Gram matrices are kept **exact and rational**; the determinant-1
    convention is carried by the *scale* instead of the matrix, using
    `gramTheta(M/D^(1/n), t) = gramTheta(M, t/D^(1/n))`, so no
    irrational entry enters the enumeration.
  * `lambda_min_lower` is a **certified rational lower bound** for
    `lambda_min`, verified by Sylvester's criterion in exact
    arithmetic on `M - mu I`.
  * every shift is canonicalized into `[-1/2, 1/2]^d` exactly, which
    is what makes the coordinate bound `|x_i| <= 1/2` in the tail
    estimate true.
  * the omitted infinite sum is majorized in closed form: the
    one-dimensional Gaussian tail by its first omitted term over a
    valid geometric ratio, the remainder included.
  * **every floating quantity is an Arb ball** (`python-flint`): pi,
    determinant roots, couplings, quadratic forms, exponentials,
    finite sums, the geometric tail, logarithms, differences and
    quotients all carry rigorous radii, so each mass, defect, slack,
    residual and duality comparison is an outward-rounded enclosure.
    There is no ad hoc floating-point allowance anywhere.
  * working precision escalates automatically until the sign that a
    row claims is decided by those enclosures. The word "certified"
    is used only for a **sign** decided that way -- never for a digit
    string.

The algebraic audit (`audit`) is a different kind of object: an exact
but **unformalized** mathematical argument, of which only the
Chinese-remainder arithmetic is executed here. It excludes the one
structural mechanism -- an integral isometry inducing the CRT
dilation -- in **every** positive rank, by an integral-idempotent
argument. What it leaves open is an accidental equality of Gaussian
masses with no inducing isometry.
"""

import argparse
import itertools
import json
import pathlib
import sys
from fractions import Fraction

import flint
from flint import arb, ctx

FLINT_VERSION = flint.__version__

# ---------------------------------------------------------------- forms

RAW_FORMS = {
    "square2": [["1", "0"], ["0", "1"]],
    "hexagonal": [["1/3", "-1/6"], ["-1/6", "1/3"]],
    "cubic3": [["1", "0", "0"], ["0", "1", "0"], ["0", "0", "1"]],
    "fcc": [["2", "1", "1"], ["1", "2", "1"], ["1", "1", "2"]],
}


def frac_matrix(rows):
    return [[Fraction(x) for x in row] for row in rows]


def diagonal_form(n, ratio):
    """diag(1, r, ..., r^(n-1)) -- normalized it is the axis-ratio
    family, the normalization being carried by the scale."""
    r = Fraction(ratio)
    return [[r**i if i == j else Fraction(0) for j in range(n)] for i in range(n)]


def shear_form(t):
    """Unimodular shear of the square lattice, determinant 1."""
    t = Fraction(t)
    return [[Fraction(1), t], [t, 1 + t * t]]


def det_frac(m):
    """Exact determinant by cofactor expansion (ranks <= 4 here)."""
    n = len(m)
    if n == 1:
        return m[0][0]
    total = Fraction(0)
    for j in range(n):
        if m[0][j] == 0:
            continue
        minor = [row[:j] + row[j + 1 :] for row in m[1:]]
        total += ((-1) ** j) * m[0][j] * det_frac(minor)
    return total


def leading_minors_positive(m):
    """Sylvester's criterion, exact."""
    n = len(m)
    for k in range(1, n + 1):
        block = [row[:k] for row in m[:k]]
        if det_frac(block) <= 0:
            return False
    return True


def lambda_min_lower(m, steps=40):
    """Certified rational lower bound for the smallest eigenvalue.

    `M - mu I` is checked for positive definiteness in exact rational
    arithmetic; any `mu` that passes is a valid lower bound. The
    bisection affects sharpness only, never validity."""
    n = len(m)
    assert leading_minors_positive(m), "form is not positive definite"
    lo = Fraction(0)
    hi = max(m[i][i] for i in range(n)) + 1
    for _ in range(steps):
        mid = (lo + hi) / 2
        shifted = [
            [m[i][j] - (mid if i == j else 0) for j in range(n)] for i in range(n)
        ]
        if leading_minors_positive(shifted):
            lo = mid
        else:
            hi = mid
    return lo


def invert_frac(m):
    """Exact inverse of a rational matrix, by cofactors."""
    n = len(m)
    d = det_frac(m)
    out = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            minor = [[m[r][c] for c in range(n) if c != i] for r in range(n) if r != j]
            out[i][j] = ((-1) ** (i + j)) * det_frac(minor) / d
    return out


def canonical_shift(x):
    """Representative of `x` in `[-1/2, 1/2]`, exactly."""
    x = Fraction(x)
    k = (x + Fraction(1, 2)).__floor__()
    y = x - k
    if y > Fraction(1, 2):
        y -= 1
    return y


# ------------------------------------------------------- ball arithmetic

UNIT_INTERVAL = None  # the ball [0, 1]; rebuilt whenever precision changes


def set_precision(bits):
    global UNIT_INTERVAL
    ctx.prec = bits
    UNIT_INTERVAL = arb("0.5", "0.5")


def ball(f):
    """Enclosure of an exact rational."""
    f = Fraction(f)
    return arb(f.numerator) / arb(f.denominator)


def scale_factor(m):
    """`D^(1/n)`: the determinant-1 convention, moved to the scale."""
    d = det_frac(m)
    assert d > 0
    return ball(d) ** (arb(1) / arb(len(m)))


def coupling(m, normalized_scale):
    """Effective coupling for the exact form at a normalized scale."""
    return normalized_scale / scale_factor(m)


def one_dim_tail(c, radius):
    """Enclosure of an upper bound for
    `sum_{|t| > R} exp(-c (|t| - 1/2)^2)`.

    Consecutive terms beyond `R` shrink by at least `exp(-2c(R+1))`,
    so the whole infinite tail is at most the first omitted term over
    `1 - that ratio`."""
    first = (-c * (arb(radius) + arb("0.5")) ** 2).exp()
    ratio = (-2 * c * (arb(radius) + 1)).exp()
    assert ratio < 1, "geometric majorant not decided at this radius"
    return 2 * first / (1 - ratio)


def one_dim_total(c):
    """Enclosure of an upper bound for
    `sum_{t in Z} exp(-c (|t| - 1/2)^2)`."""
    first = (-c / 4).exp()
    ratio = (-2 * c).exp()
    assert ratio < 1, "geometric majorant not decided"
    return 1 + 2 * first / (1 - ratio)


def tail_ball(m, beta, radius, mu):
    """Enclosure of an upper bound for the omitted mass outside the
    sup-norm box of the given radius.

    With `mu <= lambda_min(M)` and `|x_i| <= 1/2`, every omitted point
    has `Q(x+k) >= mu * sum_i (x_i + k_i)^2` and some `|k_i| > R`, so
    the omitted sum is at most `d * T(R) * S^(d-1)`."""
    n = len(m)
    c = beta * ball(mu)
    return n * one_dim_tail(c, radius) * one_dim_total(c) ** (n - 1)


def box_radius(m, beta, mu, target):
    """Smallest radius whose majorized tail is *decided* below the
    target by ball arithmetic."""
    r = 2
    while r < 600:
        try:
            if tail_ball(m, beta, r, mu) < target:
                return r
        except AssertionError:
            pass
        r += 1
    raise AssertionError("no radius reaches the tail target")


def mass_ball(m, beta, shift, mu, target):
    """Enclosure of `sum_k exp(-beta Q(shift + k))`, infinite sum
    included: the box sum is a ball, and the omitted mass lies in
    `[0, majorant]`, adjoined as `[0,1] * majorant`."""
    n = len(m)
    x = [canonical_shift(v) for v in shift]
    xb = [ball(v) for v in x]
    radius = box_radius(m, beta, mu, target)
    mb = [[ball(m[i][j]) for j in range(n)] for i in range(n)]
    total = arb(0)
    for k in itertools.product(range(-radius, radius + 1), repeat=n):
        y = [xb[i] + k[i] for i in range(n)]
        q = arb(0)
        for i in range(n):
            yi = y[i]
            for j in range(n):
                q += mb[i][j] * yi * y[j]
        total += (-beta * q).exp()
    omitted = tail_ball(m, beta, radius, mu) * UNIT_INTERVAL
    return {"ball": total + omitted, "radius": radius}


# ------------------------------------------------- the two statistics


def defect_ball(m, s, a, b, mu, target):
    """Enclosure for `D_s(a,b)`; the slack is its negation."""
    scales = {
        "a": arb(a) ** 2 * s,
        "b": arb(b) ** 2 * s,
        "one": s,
        "ab": (arb(a) * arb(b)) ** 2 * s,
    }
    enc = {
        k: mass_ball(m, coupling(m, v), [Fraction(0)] * len(m), mu, target)
        for k, v in scales.items()
    }
    d = (
        enc["a"]["ball"].log()
        + enc["b"]["ball"].log()
        - enc["one"]["ball"].log()
        - enc["ab"]["ball"].log()
    )
    return {
        "defect": d,
        "slack": -d,
        "radius": max(e["radius"] for e in enc.values()),
    }


def residual_scan(m, s, a, b, mu, target):
    """The sampled reflection failure, with the reference mass at the
    origin.

    Two distinct objects are returned, and they are not the same
    claim:

      * `residual` -- an enclosure of the **maximum** over every
        sampled class, folded with Arb's interval maximum, so it
        encloses the true maximum whether or not the individual
        comparisons are decided;
      * `witness` -- one class whose own residual enclosure is
        reported, promoted only on a *decided* strict increase. It is
        a witness, not a certified argmax: overlapping enclosures
        leave the ordering undecided, so nothing here claims that the
        witness attains the maximum."""
    n = len(m)
    beta = coupling(m, (arb(a) * arb(b)) ** 2 * s)
    c2 = 2 * beta
    ref = mass_ball(m, c2, [Fraction(0)] * n, mu, target)
    largest = None
    witness = None
    for r in itertools.product(range(b), repeat=n):
        for c in itertools.product(range(a), repeat=n):
            for e in itertools.product(range(2), repeat=n):
                vr = [Fraction(r[i], b) for i in range(n)]
                vc = [Fraction(c[i], a) for i in range(n)]
                ve = [Fraction(e[i]) for i in range(n)]
                plus = [(vr[i] + vc[i] + ve[i]) / 2 for i in range(n)]
                minus = [(vr[i] - vc[i] + ve[i]) / 2 for i in range(n)]
                gap = abs(
                    mass_ball(m, c2, plus, mu, target)["ball"]
                    - mass_ball(m, c2, minus, mu, target)["ball"]
                )
                largest = gap if largest is None else largest.max(gap)
                if witness is None or gap > witness["residual"]:
                    witness = {
                        "residual": gap,
                        "at": {"r": list(r), "c": list(c), "e": list(e)},
                    }
    return {
        "residual": largest,
        "residual_rel": largest / ref["ball"],
        "witness": witness,
        "reference_mass": ref["ball"],
    }


def duality_ball(m, s, a, b, mu, target):
    """Convention check: the defect at `M` and scale `s` against the
    defect at `M^-1` and the reflected scale `pi^2/((ab)^2 s)`.

    This checks the half-domain convention at the sampled point; it
    does not sample the other side of the domain."""
    inv = invert_frac(m)
    mu_inv = lambda_min_lower(inv)
    lhs = defect_ball(m, s, a, b, mu, target)["defect"]
    rs = arb.pi() ** 2 / ((arb(a) * arb(b)) ** 2 * s)
    rhs = defect_ball(inv, rs, a, b, mu_inv, target)["defect"]
    return abs(lhs - rhs) / abs(lhs)


# --------------------------------------------------- algebraic audit


def crt_involution(a, b):
    """The unit `u mod 2ab` with `u = 1 mod 2b` and `u = -1 mod a`."""
    from math import gcd

    assert a > 1 and b > 1, "the pair must be nontrivial"
    assert a % 2 == 1, "orient the coprime pair with a odd"
    assert gcd(a, b) == 1 and gcd(a, 2 * b) == 1, "moduli must be coprime"
    L = 2 * a * b
    for u in range(L):
        if u % (2 * b) == 1 % (2 * b) and u % a == (a - 1) % a:
            assert (u * u - 1) % L == 0, "u is not an involution"
            assert u % L not in (1 % L, (L - 1) % L), "u is trivial"
            return u
    raise AssertionError("no CRT involution")


def isometry_audit(a, b):
    """The isometry mechanism is impossible in every positive rank.

    Exact but **unformalized** argument; the executable part is only
    the Chinese-remainder arithmetic. Suppose `S` in `GL_d(Z)`,
    `d >= 1`, has finite order and induces the CRT dilation:

        S = u I  (mod L),   L = 2ab,   u = 1 (mod 2b),  u = -1 (mod a).

    Since `u^2 = 1 (mod L)`, `S^2 = I (mod L)`, and `S^2` has finite
    order, so `S^2 = I` by Minkowski's lemma -- the kernel of
    `GL_d(Z) -> GL_d(Z/L)` is torsion-free for `L >= 3`; this script
    does not verify that lemma. Now set

        P = (I - S) / 2.

    Because `u = 1 (mod 2b)` we have `S = I (mod 2b)`, so `I - S` is
    `2b` times an integral matrix and `P` is integral and divisible
    by `b`. Because `S^2 = I`,

        P^2 = (I - 2S + S^2)/4 = (2I - 2S)/4 = P,

    so `P` is an integral idempotent divisible by `b > 1`. Writing
    `P = bN`, idempotency gives `N = bN^2`, so `b` divides `N`;
    substituting repeatedly makes `N` divisible by every power of
    `b`, hence `N = 0` and `P = 0`. Therefore `S = I`. In positive
    rank a diagonal entry then reads `1 = u = -1 (mod a)`, so
    `a | 2` -- impossible for odd `a > 1`.

    So no such `S` exists in **any** positive rank. This closes the
    structural route entirely rather than bounding it below by a
    rank threshold; what remains open for the roadmap is an
    accidental equality of Gaussian masses with no inducing
    isometry."""
    L = 2 * a * b
    u = crt_involution(a, b)
    return {
        "a": a,
        "b": b,
        "L": L,
        "u": u,
        "u_squared_mod_L": (u * u) % L,
        "u_mod_2b": u % (2 * b),
        "u_mod_a": u % a,
        "projector_divisor": b,
        "a_divides_two": (2 % a == 0),
        "excluded_in_every_positive_rank": True,
        "status": "exact, unformalized argument; excludes the mechanism "
        "in every positive rank",
    }


# ------------------------------------------------------- the record


def form_entries(max_rank):
    """The sampled families, exact and rational."""
    out = [(k, frac_matrix(v)) for k, v in RAW_FORMS.items()]
    out += [(f"diag2_r{r}", diagonal_form(2, r)) for r in (2, 4, 16, 64)]
    out += [(f"shear_t{t}", shear_form(Fraction(t))) for t in ("1/4", "1/2", "1", "2")]
    out += [(f"diag3_r{r}", diagonal_form(3, r)) for r in (2, 5)]
    return [(k, v) for k, v in out if len(v) <= max_rank]


def self_dual_scale(a, b):
    return arb.pi() / (arb(a) * arb(b))


def show(x, digits=12):
    """Serialize a ball as midpoint +/- radius."""
    return x.str(digits, radius=True)


RECORD_CONFIG = {
    "scalar_scan": [
        {"pair": [3, 2], "max_rank": 3},
        {"pair": [5, 2], "max_rank": 3},
    ],
    "residual_profiles": [
        {"pair": [3, 2], "form": "square2", "multiples": [1, 4, 16, 32, 64]},
        {"pair": [3, 2], "form": "hexagonal", "multiples": [1, 4, 16]},
        {"pair": [3, 2], "form": "diag2_r64", "multiples": [1]},
        {"pair": [3, 2], "form": "cubic3", "multiples": [1, 4]},
        {"pair": [3, 2], "form": "fcc", "multiples": [1, 4]},
        {"pair": [5, 2], "form": "square2", "multiples": [1, 4, 16]},
        {"pair": [5, 2], "form": "hexagonal", "multiples": [1, 4, 16]},
    ],
    "symmetry_pairs": [
        {"pair": [3, 2], "plain": "square2", "dense": "hexagonal"},
        {"pair": [3, 2], "plain": "cubic3", "dense": "fcc"},
    ],
    "symmetry_multiples": [1, 4],
    "audit_pairs": [[3, 2], [5, 2], [5, 3], [5, 4], [7, 2], [9, 2], [7, 4]],
    "start_prec_bits": 96,
    "max_prec_bits": 3072,
    "tail_target_exp": -30,
    "duality_target_exp": -12,
}


def escalate(compute, decided, start=None, cap=None):
    """Run `compute` at increasing precision until `decided` accepts
    the result; return the result and the precision used."""
    prec = start or RECORD_CONFIG["start_prec_bits"]
    cap = cap or RECORD_CONFIG["max_prec_bits"]
    while True:
        set_precision(prec)
        target = arb(10) ** RECORD_CONFIG["tail_target_exp"]
        out = compute(target)
        if decided(out):
            return out, prec
        if prec >= cap:
            raise AssertionError(f"undecided at {prec} bits")
        prec *= 2


def scalar_row(m, s_mult, a, b, mu):
    """A scalar-slack row with a sign-certified positive slack."""

    def compute(target):
        s = self_dual_scale(a, b) * arb(s_mult)
        return defect_ball(m, s, a, b, mu, target)

    out, prec = escalate(compute, lambda o: o["slack"] > 0)
    return out, prec


def build_record(verbose=True):
    """The whole committed summary, deterministically, in one run."""
    record = {
        "meta": {
            "script": "recon/rigidity.py",
            "python_flint": FLINT_VERSION,
            "arithmetic": "Arb balls; every reported quantity is an "
            "outward-rounded enclosure",
            "certification": {
                "forms": "exact rational Gram matrices",
                "shifts": "canonicalized into [-1/2, 1/2]^d exactly",
                "lambda_min": "certified rational lower bound (Sylvester)",
                "tail": "closed-form infinite majorant, adjoined as [0,1]*T",
                "signs": "decided by the enclosures; precision escalates until decided",
            },
            "config": RECORD_CONFIG,
        },
        "scalar_scan": [],
        "duality_checks": [],
        "residual_profiles": [],
        "symmetry_crossover": [],
        "audit": [],
    }
    lam = {}
    for job in RECORD_CONFIG["scalar_scan"]:
        a, b = job["pair"]
        rows = []
        for name, m in form_entries(job["max_rank"]):
            mu = lam.setdefault(name, lambda_min_lower(m))
            out, prec = scalar_row(m, 1, a, b, mu)
            rows.append(
                {
                    "form": name,
                    "rank": len(m),
                    "slack": show(out["slack"]),
                    "slack_positive_certified": bool(out["slack"] > 0),
                    "prec_bits": prec,
                    "box_radius": out["radius"],
                }
            )
            dual_out, dual_prec = escalate(
                lambda t, m=m, a=a, b=b, mu=mu: duality_ball(
                    m, self_dual_scale(a, b), a, b, mu, t
                ),
                lambda o: o < arb(10) ** RECORD_CONFIG["duality_target_exp"],
            )
            record["duality_checks"].append(
                {
                    "pair": [a, b],
                    "form": name,
                    "s_over_star": "1",
                    "relative_difference": show(dual_out, 6),
                    "below_1e-12_certified": True,
                    "prec_bits": dual_prec,
                }
            )
            if verbose:
                print(
                    f"    ({a},{b}) {name:>12s} rank {len(m)}"
                    f"  slack {show(out['slack'], 8)}"
                    f"  [{prec} bits]  duality {show(dual_out, 3)}"
                )
        record["scalar_scan"].append(
            {
                "pair": [a, b],
                "scale": "self-dual s* = pi/(ab)",
                "row_order": "form_entries enumeration order; no numeric "
                "sort, so no binary float enters the record",
                "rows": rows,
            }
        )
    forms = dict(form_entries(4))
    for job in RECORD_CONFIG["residual_profiles"]:
        a, b = job["pair"]
        m = forms[job["form"]]
        mu = lam.setdefault(job["form"], lambda_min_lower(m))
        for k in job["multiples"]:
            out, prec = scalar_row(m, k, a, b, mu)

            def compute(target, k=k, m=m, a=a, b=b, mu=mu):
                s = self_dual_scale(a, b) * arb(k)
                return residual_scan(m, s, a, b, mu, target)

            res, res_prec = escalate(
                compute,
                lambda o: o["residual"] > 0 and o["witness"]["residual"] > 0,
                start=prec,
            )
            row = {
                "pair": [a, b],
                "form": job["form"],
                "rank": len(m),
                "s_over_star": str(k),
                "slack": show(out["slack"]),
                "slack_positive_certified": bool(out["slack"] > 0),
                "slack_prec_bits": prec,
                "residual": show(res["residual"]),
                "residual_meaning": "enclosure of the maximum over the "
                "sampled classes (Arb interval max fold)",
                "residual_positive_certified": bool(res["residual"] > 0),
                "residual_rel": show(res["residual_rel"]),
                "residual_prec_bits": res_prec,
                "witness_at": res["witness"]["at"],
                "witness_residual": show(res["witness"]["residual"]),
                "witness_positive_certified": bool(res["witness"]["residual"] > 0),
                "witness_meaning": "one class with a certified positive "
                "residual; not a certified argmax",
                "reference_mass": show(res["reference_mass"], 8),
            }
            record["residual_profiles"].append(row)
            if verbose:
                set_precision(res_prec)
                ratio = res["residual"] / out["slack"].sqrt()
                print(
                    f"    ({a},{b}) {job['form']:>12s} s/s* = {k!s:>3s}"
                    f"  slack {show(out['slack'], 6)}"
                    f"  residual {show(res['residual'], 6)}"
                    f"  res/sqrt(slack) {show(ratio, 5)}"
                )
    for job in RECORD_CONFIG["symmetry_pairs"]:
        a, b = job["pair"]
        mp, md = forms[job["plain"]], forms[job["dense"]]
        mu_p = lam.setdefault(job["plain"], lambda_min_lower(mp))
        mu_d = lam.setdefault(job["dense"], lambda_min_lower(md))
        for k in RECORD_CONFIG["symmetry_multiples"]:

            def compute(target, k=k, a=a, b=b, md=md, mp=mp, mu_d=mu_d, mu_p=mu_p):
                s = self_dual_scale(a, b) * arb(k)
                return (
                    defect_ball(md, s, a, b, mu_d, target)["slack"]
                    - defect_ball(mp, s, a, b, mu_p, target)["slack"]
                )

            gap, prec = escalate(compute, lambda o: o > 0 or o < 0)
            sign = "dense larger" if gap > 0 else "plain larger"
            record["symmetry_crossover"].append(
                {
                    "pair": [a, b],
                    "plain": job["plain"],
                    "dense": job["dense"],
                    "s_over_star": str(k),
                    "slack_dense_minus_plain": show(gap),
                    "sign_certified": sign,
                    "prec_bits": prec,
                }
            )
            if verbose:
                print(
                    f"    ({a},{b}) {job['dense']:>9s} - {job['plain']:<8s}"
                    f" s/s* = {k!s:>2s}  {show(gap, 6):>24s}"
                    f"  {sign}"
                )
    for a, b in RECORD_CONFIG["audit_pairs"]:
        rec = isometry_audit(a, b)
        record["audit"].append(rec)
        if verbose:
            print(
                f"    a = {rec['a']}, b = {rec['b']}, L = {rec['L']},"
                f" u = {rec['u']},"
                " isometry excluded in every positive rank"
            )
    return record


# --------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("task", choices=["record", "audit"])
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    set_precision(RECORD_CONFIG["start_prec_bits"])
    if args.task == "audit":
        print("== isometry mechanism audit (exact, unformalized) ==")
        for a, b in RECORD_CONFIG["audit_pairs"]:
            rec = isometry_audit(a, b)
            print(
                f"    a = {rec['a']}, b = {rec['b']}, L = {rec['L']},"
                f" u = {rec['u']},"
                " isometry excluded in every positive rank"
            )
        return 0
    print("== two-grid rigidity record (Arb ball arithmetic) ==")
    record = build_record()
    if args.write:
        path = pathlib.Path(__file__).parent / "data" / "rigidity_two_grid.json"
        path.write_text(json.dumps(record, indent=2) + "\n")
        print(f"\n  wrote {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
