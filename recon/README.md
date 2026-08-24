# Reconnaissance

Numerical evidence for the frontier questions — never proof.
`lake build` remains the only definition of done for mathematics;
this directory produces the *numerical record* the main README
cites, as reviewable code and committed summary data instead of
remembered sessions. Certified tails and interval linear algebra
(roadmap target 5) will harden it later; until then every cutoff
is a documented heuristic.

## Conventions

These are the conventions whose earlier absence produced real
errors (wrong reflection center, reversed eigenvalue orientation),
now encoded once and enforced by executable self-tests.

- **Determinant normalization.** Every Gram matrix is scaled to
  `det M = 1` before profiling. Example of why: the repo's raw
  hexagonal form `(a² − ab + b²)/3` has determinant `1/12` and its
  own reflection center at `β = π·√12`; normalized, the center is
  `π` for every form, and dual pairs are comparable.
- **Scale variable.** `u = log β`; the duality center is
  `u = log π`.
- **Statistics.** `H(u) = log Z(eᵘ)` with
  `Z(β) = Σ_{x∈ℤⁿ} exp(−β·xᵀMx)`;
  `H′(u) = −β·⟨E⟩`, `H″(u) = β²·Var(E) − β·⟨E⟩` under the Gibbs
  weight at inverse temperature `β`. Strict Q5 at a form is
  `H″ > 0` everywhere — equivalently the scale-free ratio
  `r(u) = β·Var(E)/⟨E⟩ > 1`, which is the reported statistic
  (unlike `H″`, it does not decay at large coupling, so its
  minimum is meaningful).
- **Duality.** The dual form has Gram `M⁻¹` (determinant-1 is
  preserved). Rank-two caveat: with `J = [[0,−1],[1,0]] ∈ GL₂(ℤ)`
  every det-1 symmetric `2×2` matrix satisfies `JᵀMJ = M⁻¹` — at
  rank two every form here is integrally isodual, so `L`
  versus `L*` agreement checks matrix inversion and basis
  invariance only; genuinely distinct dual pairs first appear at
  rank 3. Poisson summation gives
  `Z_L(β) = (π/β)^{n/2}·Z_{L*}(π²/β)`, hence
  `H_L″(u) = H_{L*}″(2·log π − u)`: sweeping `u ≥ log π` on both
  `L` and `L*` covers the whole line. Lean witness at rank one:
  `theta_duality_real`; the higher-rank identity is roadmap
  target 1 and is *checked numerically* here (self-test).
- **Q4 orientation** (implemented in `q4.py`): CND is controlled
  by the **largest** eigenvalue of the pairing restricted to the
  zero-sum subspace (CND iff `≤ 0`); deficit-PSD by the ordinary
  **smallest** eigenvalue of the deficit (PSD iff `≥ 0`).

## Anchors

`python3 recon/harness.py selftest` reproduces, at working
precision, two classes of anchors — if a convention is
mis-encoded, an anchor breaks.

Lean-backed anchors (rank one; each is a theorem in the tree):

| Anchor | Lean witness |
|---|---|
| `H′(log π) = −1/4` | `thetaDeriv_pi` |
| `H′(u) + H′(2·log π − u) = −1/2` | `theta_logDeriv_dual` |
| `H″` = derivative of `H′` (finite difference) | `hasDerivAt_thetaDeriv` |

Higher-rank consistency checks (numerical only — no Lean witness
yet; higher-rank duality is roadmap target 1, and its rank-one
shadow is `theta_duality_real`):

| Check | Status |
|---|---|
| hexagonal Poisson duality at `β = 2` (rank 2) | numerical |
| FCC/BCC Poisson duality at `β = 2` (rank 3) | numerical |
| self-dual center `H′(log π) = −n/4` (hexagonal, cubic) | numerical |

## Data policy

Committed: the harness, this document, and small machine-readable
summaries in `data/` (per-form profile minima, center values,
`λ₁(L)·λ₁(L*)`, grid and precision parameters — everything needed
to cite or reproduce). Never committed: raw sweep dumps.
Numerical values in `data/` are stored as strings to preserve
precision.

## Running

    nu tasks.nu recon          # self-tests + committed sweeps
    uv run recon/harness.py selftest
    uv run recon/harness.py sweep --form hexagonal
    uv run recon/harness.py family --family shear_half
    uv run recon/harness.py finescan --family fcc_squash --member y0.10 \
        --window 1.4 --finestep 0.002 --dps 30
    uv run recon/rigidity.py audit
    uv run recon/rigidity.py record            # print only
    uv run recon/rigidity.py record --write    # regenerate the record

`rigidity.py` takes no numeric flags: its sampling grid is the
`RECORD_CONFIG` literal in the script and its precision escalates on
its own, so `record --write` is deterministic — two runs produce a
byte-identical file.

Dependencies are pinned in each script's inline metadata (PEP 723:
`mpmath==1.4.1` for `harness.py` and `q4.py`, `python-flint==0.9.0`
for `rigidity.py`, recorded in every data file), so `uv run` needs
no flags. `python-flint` has no wheel for the newest interpreters,
so `rigidity.py` pins `requires-python >=3.12,<3.13` and `uv`
fetches that interpreter itself.

`harness.py` and `q4.py` enumerate lattice points over the
axis-aligned bounding box of the energy ellipsoid `Q ≤ E` —
`|xᵢ| ≤ √(E·(M⁻¹)ᵢᵢ)` with the box energy `E` set by the working
precision and the smallest coupling in use — so the box adapts
per direction and degenerating forms stay cheap. Checked
empirically at every run by an energy-stability comparison (`E`
vs `1.5E` on `H′`, `H″`, and the ratio); not a tail bound, and
certified tails are roadmap target 5. Baseline sweeps: 50-digit
precision, grid `u − log π ∈ [0, 4]` step `0.01`; families:
30 digits, step `0.02`.

## First findings (hexagonal and square, det-1, rank 2)

Both committed baseline forms satisfy `H″ > 0` at every sampled
point (401-point grid, `u − log π ∈ [0, 4]`, on `L` and `L*`
alike; duality reflects the sampled grid onto `u ≤ log π`, saying
nothing about unsampled intervals or the far tails), with the
sampled minimum of the ratio `r` attained **at the duality
center**. Isoduality makes the profile symmetric and the center
stationary — it does not force a minimum there; that the sampled
minimum sits at the center is a finding about these two forms:

| form | `λ₁(L)·λ₁(L*)` | sampled min `r` | at `u − log π` |
|---|---|---|---|
| hexagonal | `1.1547` | `3.1438` | `0` |
| square (`ℤ²`) | `1.0000` | `2.8946` | `0` |

Cross-checks: the square lattice's ratio equals the rank-one ratio
at every `u` (for identical orthogonal factors, `Var` and `⟨E⟩`
both double, so `r` is invariant — the numerical shadow of
`diagTheta_rect_strict`), and the hexagonal form's sampled
minimum is larger than the square's on this grid. Both sit far
from the Q5 boundary `r = 1`.

## Family findings (binary det-1 moduli; dps 30, step 0.02)

Two one-parameter families through the modular surface,
`M(τ) = (1/y)·[[1, x], [x, x²+y²]]` (determinant 1 by
construction; committed data `family_unit_circle_arc.json`,
`family_shear_half.json`; endpoint members reproduce the
committed baselines):

- **Unit-circle arc** `τ = e^{iφ}`, hexagonal (60°) to square
  (90°) — distinguished in `τ`-space, not by isoduality (see the
  duality caveat above):
  the sampled min `r` decreases through the seven members,
  `3.1438 → 2.8946`, every sampled minimum at the duality
  center. Hexagonal has the largest sampled margin among the
  seven arc members.
- **Shear ray** `τ = ½ + iy`, `y` descending from `√3/2`. On the
  thin tail (`y ≤ 0.18`) the product `λ₁(L)·λ₁(L*)` falls
  monotonically and the sampled min `r` collapses with it toward
  the Q5 boundary:

  | `y` | `λ₁(L)·λ₁(L*)` | sampled min `r` |
  |---|---|---|
  | `0.18` | `0.72` | `2.4345` |
  | `0.12` | `0.48` | `1.4151` |
  | `0.08` | `0.32` | `1.0377` |
  | `0.05` | `0.20` | `1.000279` |

  Away from the tail the product is *not* a single-valued
  predictor of the margin (shear `y = 0.25` has product `1` with
  ratio `3.0800`; the square has product `1` with ratio
  `2.8946`): it is a useful degeneration indicator on that
  subray, no more. At the deepest member the sampled margin
  above `r = 1` is `2.8·10⁻⁴`; the committed fine scan
  (`finescan_shear_half_y0.05.json`: window `0.3` above the
  center, step `0.0005`, both `L` and `L*`) found no
  lower sampled value away from the center. No sign change
  occurs at any sampled point of any member.

Reading (numerical, finite-sample). As `y → 0` the collapsing
direction — the primitive vector `(−1, 2)` has `Q = 4y → 0` —
acquires ever more closely spaced energy levels, so its theta
sum approaches a continuum Gaussian integral, while the
transverse cosets freeze out (their minimal energy grows like
`1/(4y)`). The continuum factor contributes `1/2` to both
`β²·Var(E)` and `β·⟨E⟩` and nothing to their difference, pinning
`r` toward `1`; after Poisson reflection the surviving
correction is the rank-one fluctuation at large reflected
coupling — the regime of `theta_fluctuation_large`. The
thin-tail data suggests asymptotic sharpness of Q5 — no uniform
margin is available to any proof — and is consistent with the
margin vanishing toward this degenerate boundary. No
counterexample appears at any sampled point.

## Rank-3 findings (first genuinely distinct dual pairs)

In rank 3 `L` and `L*` genuinely differ, and the paired-profile
protocol carries real information for the first time. Committed
data: `family_rank3_baselines.json`, `family_cubic_to_fcc.json`,
`family_fcc_squash.json`, and two fine scans. The three family
datasets use dps 30, step 0.02, span 4; each fine scan lists its
own window and step. `H″ > 0` at every sampled point of every
member and every scan.

- **Baselines.** Cubic `ℤ³` reproduces the rank-one ratio
  `2.894634` exactly (the orthogonal-sum invariance again). The
  FCC/BCC pair — dual to each other, distinct — has the largest
  sampled margin in the program so far: min `r = 3.2972` at the
  center, `λ₁(L)·λ₁(L*) = 1.2247`.
- **Cubic → FCC path** (convex combination of normalized Grams):
  sampled min `r` increases monotonically through the seven
  members, `2.8946 → 3.2972`, every minimum at the center.
- **FCC squash** (`diag(1,1,y)·M_fcc·diag(1,1,y)`,
  det-normalized): the margin collapses much faster than the
  rank-two shear, and the sampled minimum *leaves the duality
  center*, drifting outward as the form degenerates:

  | `y` | `λ₁λ₁*` | sampled min `r − 1` | at `u − log π` | side |
  |---|---|---|---|---|
  | `0.35` | `0.429` | `2.5·10⁻¹` | `0.34` | `L` |
  | `0.25` | `0.306` | `2.3·10⁻²` | `0.42` | `L` |
  | `0.15` | `0.184` | `4.7·10⁻⁵` | `0.56` | `L` |
  | `0.10` | `0.122` | `1.2·10⁻⁸` | `0.70` | `L` |
  | `0.07` | `0.086` | `2.3·10⁻¹³` | `0.80` | `L` |

  The committed fine scans (`y0.10`, `y0.07`: window `1.4`, step
  `0.002`) confirm the sampled minima and expose the first
  genuinely asymmetric dual pair: at `y = 0.10`, `L`'s sampled
  minimum is `1 + 1.2·10⁻⁸` at `u − log π ≈ 0.694` while `L*`'s
  is `1 + 7.4·10⁻⁴` at the center — different profiles, as only
  rank ≥ 3 allows. Margins remain above the energy-stability
  tolerance (`10⁻²²`), so the reported values are resolved, and
  no sign change occurs at any sampled point.

Reading (numerical, finite-sample). Squashing one direction of a
rank-3 form leaves a *rank-two* transverse lattice rather than
rank one; after determinant normalization the transverse block's
effective scale moves with `y`, which is consistent with the
observed drift of the minimum (`≈ 0.3·log(1/y)` on these
samples), and the residual margin decays roughly exponentially
in the drifted effective coupling — far faster than the
rank-two shear's collapse. The data remains consistent with
strict positivity everywhere and with margins vanishing toward
degenerate boundaries; nothing sampled contradicts Q5. The
sampled minimum sitting on one side (`L`) at an off-center
location is the concrete, measurable sense in which the
conjecture's hard regime is *not* centered at the self-dual
point once genuine dual asymmetry exists.

## Q4 phase geometry (first runs)

`recon/q4.py` implements the Q4 orientation conventions with its
own anchors — Lean-backed `pairing_pos`, `pairing_lt_base`,
`pairing_cnd_large` (the `s ≥ 1` theorem, checked as an
inequality on sampled scales), and the exact zero-sum identity
`quadFormOn_pairing_eq` (zero residual); numerical: the
`tendsto_exp_mul_pairing` limit, loosely. Committed sweeps on
the first `k` primes, log grid `s ∈ [0.02, 1.5]`, 160 points,
dps 30, crossings bisected (`q4_sweep_*.json`):

| `k` | CND crossing | PSD crossing | sign changes (CND / PSD) |
|---|---|---|---|
| 3 | `0.0803` | `0.0846` | 1 / 1 |
| 5 | `0.1079` | `0.1692` | 1 / 1 |
| 7 | `0.1268` | `0.2797` | 1 / 1 |
| 10 | `0.1448` | `0.3850` | 1 / 1 |
| 15 | `0.1608` | `0.4845` | 1 / 1 |

Findings, finite-sample. Every sampled set shows one detected
sign change per statistic on its grid, each bracket bisected —
two crossings inside one grid cell, or tangential zeros, would
go undetected. On these samples the valid-scale sets look like
upper intervals; intervality survives its first falsification
attempt and remains unproven. The historically cited
transitions (`0.080`/`0.085` on `{2,3,5}`, `0.108`/`0.169` on
five primes) and the `s = 0.12` five-prime witness (CND stat
`−0.0374`, PSD stat `−0.1284`: CND holds, PSD fails) now
reproduce from committed code (`q4_witness.json`) — the
provenance gap on the main README's oldest numerics is closed.
The two clauses separate further with set size: CND crossings
decelerate (`0.080 → 0.161`, consistent with the proven
`sup_P s_c(P) ≤ 1`), while deficit-PSD crossings grow steadily
(`0.085 → 0.484`) — and no uniform bound can hold, though each
fixed finite set may still have a finite eventual-PSD bound.
Define, analogously to `s_c(P)`,
`s_PSD(P) := inf { s₀ : the deficit on P is PSD for all s ≥ s₀ }`.
**The star obstruction** (now a theorem: `deficit_not_psd`,
`cnd_not_psd`): fix `s`, put `a = F(1)`, `b = F(2)`; the
deficit of `{2, q₁, …, qₙ}` with large satellites tends
entrywise to the star matrix (diagonal `a`, spokes `b`), whose
smallest eigenvalue is `a − √n·b` — negative once
`n > (F(1)/F(2))²`. So at every fixed scale some finite prime
set has non-PSD deficit: `sup_P s_PSD(P) = ∞`, and there is no
uniform PSD threshold. Combined with `pairing_cnd_large`, the
converse CND ⇒ deficit-PSD fails at every scale `s ≥ 1`, not
merely at the `s = 0.12` witness. At `s = 1`,
`(F(1)/F(2))² ≈ 253` — far beyond these sweeps, which see only
the star mechanism's finite-size shadow. The same mechanism
predicts the leading rate: at large `s`, `F(1) ~ 2e^{−s}` and
`F(2) ~ 2e^{−4s}`, so the critical satellite count scales as
`e^{6s}` and `s_PSD ~ (1/6)·log n` — consistent with the
15-prime crossing already near `0.484` (`(1/6)·log 14 ≈ 0.44`).
The open questions are the star-obstruction rate beyond leading
order and intervality. A new instrument for both: by the exact
identity (`quadFormOn_deficit_eq_neg`) the CND and deficit-PSD
statistics agree on the zero-sum subspace, giving a dichotomy —
a CND failure is itself a zero-sum deficit-PSD failure, while if
CND holds and deficit-PSD fails, every negative direction has
nonzero mean. Sweeps therefore record the mean component of the
minimal deficit eigenvector, to see which mechanism binds.

## Star-rate findings (dps 15, `q4_star_rate.json`)

Purpose-built star sets `{2} ∪ (n primes ≥ 100)`, PSD crossings
bisected, minimal deficit eigenvectors inspected:

| `n` | PSD crossing | exact star model | `(1/6)·log n` | mean comp |
|---|---|---|---|---|
| 4 | `0.19636` | `0.19636` | `0.23105` | `0.31623` |
| 8 | `0.37092` | `0.37092` | `0.34657` | `0.43096` |
| 16 | `0.51752` | `0.51752` | `0.46210` | `0.51450` |
| 32 | `0.64816` | `0.64816` | `0.57762` | `0.57322` |
| 64 | `0.77025` | `0.77025` | `0.69315` | `0.61394` |
| 96 | `0.83925` | `0.83925` | `0.76073` | `0.63166` |

Findings, finite-sample:

1. The two-parameter star model `log θ(s) = √n·log θ(4s)`
   reproduces the measured crossing to all printed digits at
   every sampled `n`, and satellite-base dependence dies by
   base 30 (`0.51227` from base 3, `0.51752` from base 30 and
   300 alike): above saturation the measured crossings agree
   with the limiting star model to displayed precision — the
   finite matrices themselves are not exactly star. On these
   samples the crossing is described by the one-dimensional
   scalar equation.
2. The last sampled inter-point slope is
   `Δs/Δ(log n) = 0.170 ≈ 1/6`; the sampled offsets above the
   `(log n)/6` benchmark rise through `+0.078` at `n = 96` —
   these `n` are pre-asymptotic. Expanding the scalar equation
   gives `s = (log n)/6 + n^{−1/6}/3 + O(n^{−1/3})`: the
   correction is algebraic, and not yet small at these `n`.
3. The minimal eigenvector is the star eigenvector to printed
   digits: its mean component matches the closed form
   `(n − √n)/√(2n(n+1))` (`0.316228` measured vs theory at
   `n = 4`; `0.631657` vs `0.6317` at `n = 96`), the squared
   mean projection tending to `1/2` (the closed form and its
   residual are recorded per row). Neither pure component is
   negative on its own at the ideal crossing: the zero-sum part
   has nonnegative energy under CND
   (`quadFormOn_deficit_eq_neg`) and so does the pure mean
   direction — the zero mode is created by their negative
   cross-coupling.
4. On first-`k` prime sets the failing direction *transitions*:
   at `k = 3` the minimal eigenvector is nearly zero-sum (mean
   component `0.053`, with the PSD crossing `0.0846` just above
   the CND crossing `0.0803` — the CND mechanism leaking
   through), by `k = 15` it is star-like (`0.49`). On these
   samples the eigenvector geometry crosses over from
   near-zero-sum to star-like as the set grows; whether that is
   a sharp two-regime structure is not established.
5. An identification: the long-cited binding inequality
   `log θ(s) ≥ 2·log θ(4s)`, crossing near `s = 0.196`, is
   exactly the `n = 4` star model (`√4 = 2`):
   `star_prediction(4) = 0.19636`.

## Two-grid rigidity campaign (`rigidity.py`, `rigidity_two_grid.json`)

Falsify-first pass at the last open roadmap item: whether the Gram
defect of a coprime pair can vanish in positive rank. The committed
record is produced in one deterministic run
(`uv run recon/rigidity.py record --write`, wired into
`nu tasks.nu recon`), and every number in it carries an enclosure.

Two statistics per point:

- **slack** `−D_s(a,b) ≥ 0`, the scalar obstruction (four lattice
  sums; zero exactly when the two-grid criterion holds, Lean
  `gramDefect_eq_zero_iff_twoGridReflection`);
- **residual**, the largest failure of the reflection identity itself
  over the sampled classes `(r, c, e)` — the statistic a small scalar
  slack cannot stand in for. It is reported as an **Arb interval-max
  fold**, so it encloses the true maximum whether or not the
  individual comparisons are decided, alongside a separate
  `witness_at` whose own residual is certified positive. The witness
  is not claimed to be an argmax: overlapping enclosures leave the
  ordering undecided, so only the fold carries the maximum.

### What is certified, and what is not

Nothing here is a proof, and the roadmap's formal chain is Lean's
alone. Inside that limit the arithmetic is rigorous rather than
heuristic:

- Gram matrices are kept **exact and rational**; the determinant-1
  convention is carried by the *scale* instead of the matrix, using
  `gramTheta(M/D^{1/n}, t) = gramTheta(M, t/D^{1/n})`, so no
  irrational entry enters the enumeration.
- `lambda_min_lower` is a **certified rational lower bound** for
  `λ_min`, verified by Sylvester's criterion in exact arithmetic on
  `M − μI`; the bisection affects sharpness only, never validity.
- every shift is canonicalized into `[−1/2, 1/2]^d` exactly before
  enumeration, which is what makes the coordinate bound `|x_i| ≤ 1/2`
  in the tail estimate true.
- the tail bound is a genuine **upper bound for the whole omitted
  infinite sum**: the one-dimensional Gaussian tail is majorized by
  its first omitted term over a valid geometric ratio, with the
  remainder included rather than stopped at working precision.
- **every floating quantity is an Arb ball** (`python-flint`, pinned
  in the script's PEP 723 header). π, the determinant root, the
  effective coupling, each quadratic form, each exponential, the
  finite sum, the geometric tail, the logarithms, the differences and
  the quotients all carry rigorous radii. The omitted mass is
  adjoined as `[0,1]·T` with `T` the majorant ball, so the box sum's
  one-sidedness is represented rather than assumed away. There is no
  ad hoc floating-point allowance anywhere in the pipeline.
- working precision **escalates automatically** until the sign a row
  claims is decided by those enclosures, and the record stores the
  precision per row. The word *certified* is used only for a **sign**
  decided that way — never for a digit string.
- no ordinary binary float enters the record at any point, not even
  as a sort key: the scan rows keep their enumeration order.

Every row in the committed record decides at the starting precision
of 96 bits, with room to spare: at `s/s* = 64` the slack encloses to
`1.11869633948e−14 ± 7.9e−27`, twelve orders inside its own sign.
The comparisons that carry the findings below are computed as
*differences of balls*, not by comparing printed digits, so their
signs are certified in the same sense.

### Findings — in the committed samples

Sampled: pairs `(3,2)` and `(5,2)`; ranks 2 and 3; forms `square2`,
`hexagonal`, `cubic3`, `fcc`, four diagonal ratios, four shears, two
rank-3 diagonals; scales `s/s* ∈ {1, 4, 16, 32, 64}` on the profiled
forms. The half-domain convention is checked at the sampled scale for
every form in the scan (28 checks; each relative difference encloses
zero within a radius below `4e−24`, certified under `1e−12`);
the campaign samples the half-domain `s ≥ s*` and checks the
convention at reflected points — it does not sample the other side.

1. **No counterexample in the committed samples.** Every slack has a
   certified positive lower bound. At the self-dual scale, for
   `(3,2)`: `1.31507` (square), `1.33496` (hexagonal), `1.97260`
   (cubic3), `2.01608` (fcc), down to `0.05976` for the sharpest
   sampled degeneration.
2. **Symmetry does not act uniformly — the sampled profiles cross.**
   At the self-dual scale the denser member of each pair carries the
   *larger* slack: `hexagonal − square2 = +0.0198909` and
   `fcc − cubic3 = +0.0434768`. By `4s*` both inequalities have
   reversed: `−0.00940326` and `−0.0202102`. All four signs are
   certified as differences of balls (`symmetry_crossover` in the
   record). So within the samples symmetry strengthens the obstruction
   at the centre of the domain and weakens it farther into the
   large-scale chamber; it does not uniformly help or hurt, and no
   monotone reading of density against rigidity survives the crossing.
3. **Orthogonal sums add exactly**, as observed: `square2` is `2×`
   and `cubic3` is `3×` the same rank-one number `0.65753`,
   consistent with Lean's `orthSum_defect`.
4. **The only sampled route toward zero is the scale boundary.** The
   slack falls as `s → ∞` (and by duality as `s → 0`). The rank-two
   diagonal degeneration is not a separate route in these samples: at
   `det = 1` it is the orthogonal sum of two rank-one systems at
   reciprocal scales, and the numbers show it — `diag2_r16` at `s*`
   reproduces `square2` at `4s*` to all recorded digits.
5. **Observed relation between the two statistics.** Along the
   `square2` profile the ratio `residual/√slack` is `0.50006`, `0.5`,
   `0.5` at `s/s* = 16, 32, 64` — consistent with the scalar defect
   being a quadratic Cauchy–Schwarz gap in the residual. It is an
   observation on one profile, not an established identity: the
   `hexagonal` profile has not stabilized over the sampled range
   (`0.639, 0.455, 0.408`), and along the anisotropic degeneration the
   ratio runs the other way (`1.425` at `s*`).
6. **The isometry mechanism is impossible in every positive rank** —
   an exact but **unformalized** argument, of which only the
   Chinese-remainder arithmetic is executed here. Let `S ∈ GL_d(ℤ)`,
   `d ≥ 1`, have finite order and induce the CRT dilation:
   `S ≡ u·I (mod L)` with `L = 2ab`, `u ≡ 1 (mod 2b)`,
   `u ≡ −1 (mod a)`. Since `u² ≡ 1 (mod L)`, `S² ≡ I (mod L)`, and
   `S²` has finite order, so `S² = I` by Minkowski's lemma (the
   kernel of `GL_d(ℤ) → GL_d(ℤ/L)` is torsion-free for `L ≥ 3`; the
   script does not verify that lemma). Put

       P = (I − S)/2.

   From `u ≡ 1 (mod 2b)` we get `S ≡ I (mod 2b)`, so `I − S` is `2b`
   times an integral matrix and `P` is integral and divisible by `b`.
   From `S² = I`,

       P² = (I − 2S + S²)/4 = (2I − 2S)/4 = P,

   so `P` is an integral idempotent divisible by `b > 1`. Writing
   `P = bN`, idempotency gives `N = bN²`, so `b ∣ N`; substituting
   repeatedly makes `N` divisible by every power of `b`, hence
   `N = 0` and `P = 0`, i.e. `S = I`. In positive rank a diagonal
   entry then reads `1 ≡ u ≡ −1 (mod a)`, so `a ∣ 2` — impossible for
   odd `a > 1`.

   This is stronger than a rank threshold: no such `S` exists in
   **any** positive rank, so the structural route is closed outright,
   not merely out of reach of the sampled ranks.

What the campaign does not settle: ranks above 3, forms outside the
sampled families, scales outside the sampled grid, whether the
observed square-root relation has an exact statement, and — the one
route the audit leaves open — whether an equality could arise as an
accidental coincidence of Gaussian mass values, with no isometry
inducing it. That is now the whole remaining question, and it is
analytic rather than structural: within the samples the obstruction
is large away from the scale boundary, and the only mechanism that
would have produced equality by symmetry has been excluded in every
rank.
