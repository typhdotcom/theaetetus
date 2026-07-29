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

Dependencies are pinned in the script's inline metadata (PEP 723:
`mpmath==1.4.1`, recorded in every data file), so `uv run` needs
no flags. Lattice points are enumerated over the axis-aligned
bounding box of the energy ellipsoid `Q ≤ E` —
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
**The star obstruction** (analytic, not yet formalized —
roadmap target 8): fix `s`, put `a = F(1)`, `b = F(2)`; the
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
order and intervality.
