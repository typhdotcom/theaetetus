# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "mpmath==1.4.1",
# ]
# ///
"""Reconnaissance: the falsification gate for the log-mass Fourier
certificate.

Evidence, not proof. **Nothing in this file is certified.** Unlike
`recon/rigidity.py`, which uses ball arithmetic and reports only signs
its enclosures decide, this script is ordinary high-precision
floating point with a spectral quadrature whose aliasing error is
estimated empirically, not bounded. Its job is falsification: to look
for a form, chart or coupling where the certificate fails.

The object. For a positive-definite `M` and coupling `alpha`, the
logarithmic shifted mass

    L(x) = log gramMass(M, alpha, x)

is real, `Z^d`-periodic and even (Lean: `logMass`). Its Fourier
coefficients on `R^d/Z^d` are

    l_nu = integral over the unit cube of L(x) exp(-2 pi i nu . x) dx,

real and symmetric under `nu -> -nu`. Coprime rigidity is implied by
`EvenPartSeparating`, which in turn follows from `l_nu != 0` on the
finite family

    {e_i}  union  {e_i + e_j : i < j}

composed with the arithmetic step `isLatticeShift_or_of_pairwise`
(Lean). That family is the certificate this script probes.

Two cautions, and they are the point of the exercise:

  * the certificate is **chart dependent** -- the frequencies belong
    to a chosen integral chart, and the sweep includes unimodular
    recharts of the same lattice to exhibit that directly;
  * the certificate is **stronger than rigidity**. It may fail while
    target 10 remains true. A failure here refutes the certificate,
    not the roadmap item.

A small sampled coefficient is never reported as zero. Every value is
reported with the grid it was computed on and the change under
doubling that grid, and structural zeros are identified only where an
exact reference value predicts them.

Method. `L` is smooth and periodic, so the uniform trapezoidal rule
is spectrally accurate: on an `N`-point grid per axis the computed
coefficient differs from `l_nu` by the aliasing sum over
`nu + N*Z^d`, which falls off with the same Gaussian rate as the
coefficients themselves. Doubling `N` is therefore a sharp empirical
convergence test, and it is reported for every entry.

Exact references. For `M = diag(m_1, ..., m_d)` the mass factorizes,
so `L(x) = sum_i log g(x_i)` with `g` the rank-one theta, and the
Jacobi triple product gives, exactly,

    l_{k e_i} = (-1)^(k+1) q_i^k / (k (1 - q_i^(2k))),
                q_i = exp(-pi^2 / (alpha m_i)),
    l_nu      = 0    whenever nu is supported on more than one axis.

A unimodular rechart `M' = U^T M U` satisfies `L'(x) = L(Ux)`, hence
`l'_nu = l_{U^-T nu}`, so a rechart of a diagonal form inherits exact
references too -- which is what makes the sheared square lattices
sharp controls rather than merely suggestive ones.

Structure. Each form carries an **exact** decomposability audit: a
rational search for a nonzero `v` with `Z^d = Zv (+) (v-perp ∩ Z^d)`,
which happens exactly when `Q(v)` divides every entry of `Mv`. The
search bound comes from `det M = det L_1 * det L_2`, and it is
exhaustive for rank at most three, where any proper splitting has a
rank-one summand. `is_diagonal` is a chart property and is **not**
used as a proxy for decomposability.
"""

import argparse
import itertools
import json
import math
import pathlib
import sys
from fractions import Fraction

import mpmath as mp

# ------------------------------------------------------------- forms

RAW_FORMS = {
    "rank1": [["1"]],
    "square2": [["1", "0"], ["0", "1"]],
    "hexagonal": [["1/3", "-1/6"], ["-1/6", "1/3"]],
    "cubic3": [["1", "0", "0"], ["0", "1", "0"], ["0", "0", "1"]],
    "fcc": [["2", "1", "1"], ["1", "2", "1"], ["1", "1", "2"]],
}


def frac_matrix(rows):
    return [[Fraction(x) for x in row] for row in rows]


def diagonal_form(n, ratio):
    r = Fraction(ratio)
    return [
        [r**i if i == j else Fraction(0) for j in range(n)] for i in range(n)
    ]


def rechart(m, u):
    """`U^T M U` for an integral `U`: the same lattice in another
    integral chart."""
    n = len(m)
    return [
        [
            sum(
                Fraction(u[k][i]) * m[k][l] * Fraction(u[l][j])
                for k in range(n)
                for l in range(n)
            )
            for j in range(n)
        ]
        for i in range(n)
    ]


def near_diagonal(eps):
    """`[[1, eps], [eps, 1]]`: a probe approaching the decomposable
    locus, where the mixed coefficient is smallest."""
    e = Fraction(eps)
    return [[Fraction(1), e], [e, Fraction(1)]]


def shear_form(t):
    """Gram of the basis `{e1, t*e1 + e2}`. For **integral** `t` this
    is the square lattice in a different integral chart -- a unimodular
    rechart, not a different lattice."""
    t = Fraction(t)
    return [[Fraction(1), t], [t, 1 + t * t]]


def det_frac(m):
    n = len(m)
    if n == 0:
        return Fraction(1)
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
    for k in range(1, len(m) + 1):
        if det_frac([row[:k] for row in m[:k]]) <= 0:
            return False
    return True


def lambda_min_lower(m, steps=40):
    """Rational lower bound for the smallest eigenvalue, verified by
    Sylvester's criterion in exact arithmetic."""
    n = len(m)
    assert leading_minors_positive(m), "form is not positive definite"
    lo, hi = Fraction(0), max(m[i][i] for i in range(n)) + 1
    for _ in range(steps):
        mid = (lo + hi) / 2
        shifted = [
            [m[i][j] - (mid if i == j else 0) for j in range(n)]
            for i in range(n)
        ]
        if leading_minors_positive(shifted):
            lo = mid
        else:
            hi = mid
    return lo


def invert_frac(m):
    n = len(m)
    d = det_frac(m)
    out = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            minor = [
                [m[r][c] for c in range(n) if c != i]
                for r in range(n)
                if r != j
            ]
            out[i][j] = ((-1) ** (i + j)) * det_frac(minor) / d
    return out


def integralize(m):
    """Scale a rational form to an integral one. Orthogonal
    decomposability is unaffected by a positive scalar."""
    den = 1
    for row in m:
        for x in row:
            den = den * x.denominator // math.gcd(den, x.denominator)
    return [[int(x * den) for x in row] for row in m]


def split_witness(m):
    """A nonzero `v` with `Z^d = Zv (+) (v-perp ∩ Z^d)`, or `None`.

    `Z^d` splits off `Zv` orthogonally exactly when `Q(v)` divides
    every entry of `Mv`: one direction writes `e_i = c v + w` with
    `w ⊥ v`, so `<v, e_i> = c Q(v)`; the other sets
    `c = <v, x>/Q(v)`, which is then integral for every `x`.

    A rank-one summand has `Q(v) = det L_1 <= det M / lambda_min^(d-1)`,
    so the search is finite; the certified rational **lower** bound for
    `lambda_min` enlarges the box, which is the safe direction. Any
    proper splitting of a lattice of rank at most three has a rank-one
    summand, so this search is exhaustive there and **only** there."""
    n = len(m)
    assert n <= 3, "the split search is exhaustive only up to rank three"
    if n == 1:
        return None
    mi = integralize(m)
    mq = [[Fraction(x) for x in row] for row in mi]
    mu = lambda_min_lower(mq)
    bound = det_frac(mq) / mu ** (n - 1)
    span = int(math.isqrt(int(bound / mu)) + 1)
    for v in itertools.product(range(-span, span + 1), repeat=n):
        if all(t == 0 for t in v):
            continue
        mv = [sum(mi[i][j] * v[j] for j in range(n)) for i in range(n)]
        q = sum(v[i] * mv[i] for i in range(n))
        if q > bound:
            continue
        g = 0
        for e in mv:
            g = math.gcd(g, abs(e))
        if g % q == 0:
            return list(v)
    return None


def inverse_transpose_int(u):
    """`(U^T)^{-1}` for a unimodular integral `U`, exactly."""
    n = len(u)
    uq = [[Fraction(x) for x in row] for row in u]
    d = det_frac(uq)
    assert abs(d) == 1, "chart matrix must be unimodular"
    inv = invert_frac(uq)
    out = [[inv[j][i] for j in range(n)] for i in range(n)]
    for row in out:
        for x in row:
            assert x.denominator == 1
    return [[int(x) for x in row] for row in out]


def is_diagonal(m):
    return all(
        m[i][j] == 0 for i in range(len(m)) for j in range(len(m)) if i != j
    )


# -------------------------------------------------------- evaluation


def to_mp(m):
    return [[mp.mpf(x.numerator) / mp.mpf(x.denominator) for x in row]
            for row in m]


def quad(mb, y):
    n = len(mb)
    return mp.fsum(
        mb[i][j] * y[i] * y[j] for i in range(n) for j in range(n)
    )


def box_radius(alpha, mu, tol):
    """Smallest `R` with `exp(-alpha*mu*(R-1/2)^2) < tol`. An estimate
    of where the direct sum may be truncated, not a certified tail."""
    r = 2
    while r < 400:
        if mp.exp(-alpha * mu * (r - mp.mpf(1) / 2) ** 2) < tol:
            return r
        r += 1
    raise AssertionError("no truncation radius reached")


def mass_direct(mb, alpha, x, radius):
    n = len(mb)
    total = mp.mpf(0)
    for k in itertools.product(range(-radius, radius + 1), repeat=n):
        y = [x[i] + k[i] for i in range(n)]
        total += mp.exp(-alpha * quad(mb, y))
    return total


def lambda_max_upper(m):
    """Gershgorin upper bound for the largest eigenvalue, exact."""
    return max(sum(abs(m[i][j]) for j in range(len(m))) for i in range(len(m)))


def mass_dual(mb, mib, det, alpha, x, radius):
    """Poisson form: the same mass as a dual character sum. An
    independent evaluation route, used as a consistency check."""
    n = len(mb)
    pref = (mp.pi / alpha) ** (mp.mpf(n) / 2) / mp.sqrt(det)
    beta = mp.pi**2 / alpha
    total = mp.mpf(0)
    for nu in itertools.product(range(-radius, radius + 1), repeat=n):
        nuf = [mp.mpf(t) for t in nu]
        phase = 2 * mp.pi * mp.fsum(nuf[i] * x[i] for i in range(n))
        total += mp.exp(-beta * quad(mib, nuf)) * mp.cos(phase)
    return pref * total


# ------------------------------------------------- Fourier of log(m)


def frequencies(n):
    out = [tuple(1 if t == i else 0 for t in range(n)) for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            out.append(
                tuple(1 if t in (i, j) else 0 for t in range(n))
            )
    return out


def mesh_nome(alpha, lmax):
    """`exp(-pi^2 / (alpha * lambda_max))`, a **heuristic** only.

    Gershgorin bounds the Gaussian coefficients of the mass, but the
    logarithm moves the decay rate to the nearest complex zero, so
    this is not a proved bound on the tail of `log mass`. It is used
    solely to choose a mesh, and empirically tracks the observed
    convergence. Grid doubling, not this quantity, is the check."""
    return mp.exp(-mp.pi**2 / (alpha * mp.mpf(lmax.numerator)
                               / mp.mpf(lmax.denominator)))


def adapted_grid(base, q, cap):
    """Double the base grid while the heuristic estimate `q**N` stays
    above the target, up to a cap."""
    g = base
    while 2 * g < cap and q ** (2 * g) > mp.mpf(10) ** -24:
        g *= 2
    return g


def log_fourier_pair(mb, alpha, mu, grid, tol):
    """Trapezoidal (spectral) Fourier coefficients of `log mass` on the
    `2*grid` mesh and, by subsampling it, on the `grid` mesh.

    `L` is even, so values at `idx` and `-idx` coincide and only one
    representative of each pair is evaluated. Returns the coarse and
    fine coefficient dictionaries, the truncation radius, and the
    largest `|L|` seen (which sets the resolution floor)."""
    n = len(mb)
    radius = box_radius(alpha, mu, tol)
    freqs = frequencies(n)
    fine = 2 * grid
    step = mp.mpf(1) / fine
    cache = {}
    values = {}
    for idx in itertools.product(range(fine), repeat=n):
        key = min(idx, tuple((-t) % fine for t in idx))
        if key not in cache:
            x = [step * t for t in key]
            cache[key] = mp.log(mass_direct(mb, alpha, x, radius))
        values[idx] = cache[key]
    out = {}
    for label, mesh in (("coarse", grid), ("fine", fine)):
        skip = fine // mesh
        acc = {f: mp.mpf(0) for f in freqs}
        for idx in itertools.product(range(mesh), repeat=n):
            val = values[tuple(t * skip for t in idx)]
            for f in freqs:
                phase = 2 * mp.pi * mp.fsum(
                    mp.mpf(f[i]) * idx[i] for i in range(n)
                ) / mesh
                acc[f] += val * mp.cos(phase)
        total = mp.mpf(mesh) ** n
        out[label] = {f: acc[f] / total for f in freqs}
    lmax = max(abs(v) for v in cache.values())
    return out["coarse"], out["fine"], radius, lmax


def diagonal_coefficient(m, alpha, nu):
    """Exact `l_nu` for a **diagonal** form, from the Jacobi triple
    product. `L` splits as a sum of rank-one logarithms, so `l_nu`
    vanishes unless `nu` is supported on one coordinate, and there

        l_{m e_i} = (-1)^(m+1) q_i^m / (m (1 - q_i^(2m))),
        q_i = exp(-pi^2 / (alpha * M_ii)).
    """
    support = [i for i in range(len(m)) if nu[i]]
    if len(support) != 1:
        return mp.mpf(0)
    i = support[0]
    k = abs(nu[i])
    mi = mp.mpf(m[i][i].numerator) / mp.mpf(m[i][i].denominator)
    q = mp.exp(-mp.pi**2 / (alpha * mi))
    return (-1) ** (k + 1) * q**k / (k * (1 - q ** (2 * k)))


def reference_for(spec, forms, alpha, nu):
    """Exact reference for `l_nu`, when one is available.

    Directly for a diagonal form; for a unimodular rechart of a
    diagonal parent through `l'_nu = l_{U^-T nu}`, since
    `L'(x) = L(Ux)`. Returns `(value, source, parent_nu)` or
    `(None, None, parent_nu)`."""
    m = forms[spec["name"]]
    if is_diagonal(m):
        return diagonal_coefficient(m, alpha, nu), "diagonal", None
    parent = spec.get("parent")
    if parent is None:
        return None, None, None
    pm = forms[parent]
    uinv_t = inverse_transpose_int(spec["chart"])
    n = len(m)
    pnu = [sum(uinv_t[i][j] * nu[j] for j in range(n)) for i in range(n)]
    if is_diagonal(pm):
        return (
            diagonal_coefficient(pm, alpha, pnu),
            f"diagonal parent {parent} via U^-T",
            pnu,
        )
    return None, None, pnu



# ------------------------------------------------------- the sweep

SWEEP_CONFIG = {
    "dps": 30,
    "tail_tol_exp": -34,
    "jobs": [
        {"forms": ["rank1"], "grid": 12, "grid_cap": 96,
         "alpha_over_star": ["1/4", "1/2", "1", "2", "4"]},
        {"forms": ["square2", "diag2_r4", "hexagonal", "hex_chart2",
                   "hex_chart3", "shear_t1", "shear_t2", "shear_t1/2",
                   "neardiag_1/10", "neardiag_1/100"],
         "grid": 10, "grid_cap": 48,
         "alpha_over_star": ["1/4", "1/2", "1", "2"]},
        {"forms": ["diag2_r16"], "grid": 10, "grid_cap": 48,
         "alpha_over_star": ["1/4", "1/2"]},
        {"forms": ["cubic3", "fcc"], "grid": 8, "grid_cap": 16,
         "alpha_over_star": ["1", "2"]},
        {"forms": ["fcc_chart2"], "grid": 8, "grid_cap": 16,
         "alpha_over_star": ["1"]},
    ],
}


FORM_SPECS = [
    {"name": "rank1"},
    {"name": "square2"},
    {"name": "diag2_r4"},
    {"name": "diag2_r16"},
    {"name": "hexagonal"},
    {"name": "hex_chart2", "parent": "hexagonal", "chart": [[1, 1], [0, 1]]},
    {"name": "hex_chart3", "parent": "hexagonal", "chart": [[1, 2], [0, 1]]},
    {"name": "shear_t1", "parent": "square2", "chart": [[1, 1], [0, 1]]},
    {"name": "shear_t2", "parent": "square2", "chart": [[1, 2], [0, 1]]},
    {"name": "shear_t1/2"},
    {"name": "neardiag_1/10"},
    {"name": "neardiag_1/100"},
    {"name": "cubic3"},
    {"name": "fcc"},
    {
        "name": "fcc_chart2",
        "parent": "fcc",
        "chart": [[1, 1, 0], [0, 1, 0], [0, 0, 1]],
    },
]


def form_table():
    out = {k: frac_matrix(v) for k, v in RAW_FORMS.items()}
    for r in (2, 4, 16):
        out[f"diag2_r{r}"] = diagonal_form(2, r)
    for s in ("1", "2", "1/2"):
        out[f"shear_t{s}"] = shear_form(Fraction(s))
    for e in ("1/10", "1/100"):
        out[f"neardiag_{e}"] = near_diagonal(Fraction(e))
    for spec in FORM_SPECS:
        if "parent" in spec:
            out[spec["name"]] = rechart(out[spec["parent"]], spec["chart"])
    return out


def spec_table():
    return {s["name"]: s for s in FORM_SPECS}


def form_report(spec, forms):
    """The exact description of one form, for the record."""
    m = forms[spec["name"]]
    n = len(m)
    d = det_frac(m)
    w = split_witness(m)
    out = {
        "name": spec["name"],
        "rank": n,
        "gram": [[str(x) for x in row] for row in m],
        "determinant": str(d),
        "lambda_min_lower": str(lambda_min_lower(m)),
        "lambda_max_gershgorin": str(lambda_max_upper(m)),
        "structure": "decomposable" if w else "indecomposable",
        "orthogonal_split_witness": w,
        "audit": "exact rational search for a rank-one orthogonal "
        "summand; exhaustive for rank at most three",
    }
    if "parent" in spec:
        out["parent"] = spec["parent"]
        out["chart_matrix"] = spec["chart"]
        out["chart_inverse_transpose"] = inverse_transpose_int(spec["chart"])
        out["chart_note"] = "L'(x) = L(Ux), so l'_nu = l_{U^-T nu}"
    return out


def show(x, digits=10):
    return mp.nstr(x, digits)


def sweep(verbose=True):
    mp.mp.dps = SWEEP_CONFIG["dps"]
    tol = mp.mpf(10) ** SWEEP_CONFIG["tail_tol_exp"]
    arith_floor = mp.mpf(10) ** -(SWEEP_CONFIG["dps"] - 4)
    forms = form_table()
    record = {
        "meta": {
            "script": "recon/logfourier.py",
            "mpmath": mp.__version__,
            "status": "NOT CERTIFIED: ordinary high-precision floating "
            "point; the spectral quadrature error is estimated by "
            "grid doubling, not bounded",
            "certificate": "l_nu != 0 on {e_i} union {e_i+e_j, i<j} "
            "implies EvenPartSeparating; chart dependent, and "
            "strictly stronger than coprime rigidity itself",
            "reading": "a value at or below resolution_floor is NOT "
            "evidence of vanishing; structural zeros are named only "
            "where an exact reference predicts them",
            "config": SWEEP_CONFIG,
        },
        "forms": [form_report(s, forms) for s in FORM_SPECS],
        "rows": [],
        "duality_checks": [],
    }
    for job in SWEEP_CONFIG["jobs"]:
        for name in job["forms"]:
            m = forms[name]
            n = len(m)
            mu = lambda_min_lower(m)
            mb = to_mp(m)
            mib = to_mp(invert_frac(m))
            dfr = det_frac(m)
            det = mp.mpf(dfr.numerator) / mp.mpf(dfr.denominator)
            scale = det ** (mp.mpf(1) / n)
            for ratio in job["alpha_over_star"]:
                fr = Fraction(ratio)
                alpha = (
                    mp.pi
                    * mp.mpf(fr.numerator)
                    / mp.mpf(fr.denominator)
                    / scale
                )
                q = mesh_nome(alpha, lambda_max_upper(m))
                grid = adapted_grid(job["grid"], q, job["grid_cap"])
                coarse, fine, radius, lmax = log_fourier_pair(
                    mb, alpha, mu, grid, tol
                )
                specs = spec_table()
                floor = max(
                    arith_floor * max(lmax, mp.mpf(1)),
                    max(abs(fine[f] - coarse[f]) for f in frequencies(n)),
                )
                entries = []
                for f in frequencies(n):
                    v = fine[f]
                    entry = {
                        "nu": list(f),
                        "value": show(v),
                        "sign": "+" if v > 0 else "-" if v < 0 else "0",
                        "abs": show(abs(v), 6),
                        "grid_doubling_change": show(abs(v - coarse[f]), 3),
                        "below_resolution": bool(abs(v) <= 100 * floor),
                    }
                    rv, src, pnu = reference_for(
                        specs[name], forms, alpha, list(f)
                    )
                    if pnu is not None:
                        entry["parent_nu"] = pnu
                    if rv is not None:
                        entry["exact_reference"] = show(rv, 10)
                        entry["reference_source"] = src
                        entry["reference_gap"] = show(abs(v - rv), 3)
                    entries.append(entry)
                resolved = [e for e in entries if not e["below_resolution"]]
                smallest = (
                    min(resolved, key=lambda e: mp.mpf(e["abs"]))
                    if resolved
                    else None
                )
                row = {
                    "form": name,
                    "rank": n,
                    "alpha_over_star": ratio,
                    "grid": 2 * grid,
                    "box_radius": radius,
                    "mesh_nome_heuristic": show(q, 4),
                    "alpha_star": show(mp.pi / scale, 10),
                    "alpha": show(alpha, 10),
                    "diagonal": is_diagonal(m),
                    "resolution_floor": show(floor, 3),
                    "entries": entries,
                    "certificate_holds_above_resolution": len(resolved)
                    == len(entries),
                    "smallest_resolved_abs": (
                        smallest["abs"] if smallest else None
                    ),
                    "smallest_resolved_at": (
                        smallest["nu"] if smallest else None
                    ),
                }
                record["rows"].append(row)
                xprobe = [mp.mpf(1) / 3 + mp.mpf(i) / 7 for i in range(n)]
                direct = mass_direct(mb, alpha, xprobe, radius)
                dual_radius = box_radius(
                    mp.pi**2 / alpha, lambda_min_lower(invert_frac(m)), tol
                )
                dual = mass_dual(mb, mib, det, alpha, xprobe, dual_radius)
                record["duality_checks"].append(
                    {
                        "form": name,
                        "alpha_over_star": ratio,
                        "relative_difference": show(
                            abs(direct - dual) / direct, 4
                        ),
                        "probe_point": [show(v, 12) for v in xprobe],
                        "probe_note": "one point per row: x_i = 1/3 + i/7; "
                        "this compares the direct and dual representations "
                        "of the mass there, not the quadrature mesh and not "
                        "the Fourier coefficients",
                        "direct_radius": radius,
                        "dual_radius": dual_radius,
                    }
                )
                if verbose:
                    vals = "  ".join(
                        "{}:{}{}{}".format(
                            "".join(map(str, e["nu"])),
                            e["sign"],
                            e["abs"],
                            "*" if e["below_resolution"] else "",
                        )
                        for e in entries
                    )
                    print(
                        f"  {name:>14s} a/a* = {ratio:>4s} N={2 * grid:>3d}"
                        f" q~{show(q, 3):>7s} floor {show(floor, 2):>9s}"
                        f"   {vals}"
                    )
    return record


def crossings(record):
    """Sign changes of a **resolved** coefficient across the sampled
    couplings. Entries at or below the resolution floor are excluded:
    their sign is numerical noise, not a measurement."""
    out = []
    seen = {}
    for row in record["rows"]:
        for e in row["entries"]:
            if e["below_resolution"]:
                continue
            key = (row["form"], tuple(e["nu"]))
            seen.setdefault(key, []).append(
                (row["alpha_over_star"], e["sign"]))
    for key, seq in seen.items():
        signs = {s for _, s in seq}
        if len(signs) > 1:
            out.append(
                {
                    "form": key[0],
                    "nu": list(key[1]),
                    "profile": [{"alpha_over_star": a, "sign": s}
                                for a, s in seq],
                }
            )
    return out


def summarize(record):
    """Counts, split against the exact structural audit."""
    struct = {f["name"]: f["structure"] for f in record["forms"]}
    resolved = [
        r for r in record["rows"] if r["certificate_holds_above_resolution"]
    ]
    unresolved = [
        r
        for r in record["rows"]
        if not r["certificate_holds_above_resolution"]
    ]
    return {
        "rows": len(record["rows"]),
        "rows_all_frequencies_resolved_nonzero": len(resolved),
        "rows_with_an_unresolved_frequency": len(unresolved),
        "resolved_forms": sorted({r["form"] for r in resolved}),
        "unresolved_forms": sorted({r["form"] for r in unresolved}),
        "resolved_forms_all_indecomposable": all(
            struct[r["form"]] == "indecomposable" for r in resolved
        ),
        "unresolved_forms_all_decomposable": all(
            struct[r["form"]] == "decomposable" for r in unresolved
        ),
        "sign_crossings_among_resolved_entries": len(
            record["sign_crossings"]
        ),
        "caveat": "an observation on the sampled forms, charts and "
        "couplings; not a proved equivalence between the certificate "
        "and orthogonal indecomposability",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("task", choices=["sweep", "structure"])
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    forms = form_table()
    if args.task == "structure":
        print("== exact orthogonal decomposability audit (rank <= 3) ==")
        for s in FORM_SPECS:
            r = form_report(s, forms)
            print(
                f"  {r['name']:>15s}  {r['structure']:>15s}"
                f"  witness {r['orthogonal_split_witness']}"
            )
        return 0
    print("== log-mass Fourier certificate: falsification gate ==")
    print("== NOT CERTIFIED: high-precision floating point ==")
    record = sweep()
    record["sign_crossings"] = crossings(record)
    record["summary"] = summarize(record)
    s = record["summary"]
    print(
        f"\n  rows: {s['rows']};"
        f" all frequencies resolved nonzero in"
        f" {s['rows_all_frequencies_resolved_nonzero']};"
        f" an unresolved frequency in"
        f" {s['rows_with_an_unresolved_frequency']}"
    )
    print(
        f"  resolved rows all on indecomposable forms:"
        f" {s['resolved_forms_all_indecomposable']};"
        f" unresolved rows all on decomposable forms:"
        f" {s['unresolved_forms_all_decomposable']}"
    )
    print(f"  sign crossings among resolved entries:"
          f" {len(record['sign_crossings'])}")
    worst = max(
        record["duality_checks"],
        key=lambda c: mp.mpf(c["relative_difference"]),
    )
    print(f"  worst direct/dual discrepancy: {worst['relative_difference']}"
          f" ({worst['form']}, a/a* = {worst['alpha_over_star']})")
    if args.write:
        path = pathlib.Path(__file__).parent / "data" / "log_fourier.json"
        path.write_text(json.dumps(record, indent=2) + "\n")
        print(f"  wrote {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
