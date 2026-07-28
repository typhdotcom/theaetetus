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
- **Q4 orientation** (reserved for the phase-geometry sweep,
  harness v2): CND is controlled by the **largest** eigenvalue of
  the pairing restricted to the zero-sum subspace; deficit-PSD by
  the ordinary **smallest** eigenvalue of the deficit.

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
| hexagonal Poisson duality at `β = 2` | numerical |
| isodual center `H′(log π) = −n/4` | numerical |

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
    uv run recon/harness.py finescan --family shear_half --member y0.05 \
        --window 0.3 --finestep 0.0005 --radius 32 --dps 30

Dependencies are pinned in the script's inline metadata (PEP 723:
`mpmath==1.4.1`, recorded in every data file), so `uv run` needs
no flags. Defaults: 50-digit precision, cutoff radius 14 —
checked empirically at
every run by a radius-stability comparison (`R` vs `R+3` at the
duality center) plus an ad hoc decay proxy; neither is a tail
bound, and certified tails are roadmap target 5. Grid
`u − log π ∈ [0, 4]` in steps of `0.01`.

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
from the Q5 boundary `r = 1`. The shear family interpolating away
from these baseline points is the next sweep.

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
  center, step `0.0005`, radius 32, both `L` and `L*`) found no
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
