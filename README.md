# Theaetetus

*The arithmetic of coupled resolutions*

> The lines which form the sides of the oblong numbers we called
> *powers*, as not commensurable with the others in length, but only
> in the plane areas they have the power to form.
> — Plato, *Theaetetus* 147e–148b (adapted)

A Lean 4 study of **the defect**: an invariant of a positive-definite
quadratic form on a finite-rank lattice that measures the failure of
its spectrum to factor over the primes.

## The object

Let `Z_L(β)` be the Boltzmann sum of a positive-definite quadratic
form on a finite-rank lattice `L` — at rank one, the theta function
`θ(α) = ∑_{k∈ℤ} e^{−αk²}`. **The seed**: the defect of a pair of
resolutions `q, q′ ≥ 1` is the four-term cross-ratio over the
divisibility lattice,

    D(q, q′) := [log Z(q²) + log Z(q′²)] − [log Z(gcd²) + log Z(lcm²)].

On a graph carrier the analytic formula carries its intended reading
as a theorem: a resolution `q` induces a **residue action** on
`H¹(G;ℤ) ⧸ qH¹(G;ℤ)` with complexity `K(q)`, and the cross-ratio
law proves `D(q,q′) = [K(lcm) + K(gcd)] − [K(q) + K(q′)]`
(`crossRatio_law`). Deriving that reading from residue actions on
`L ⧸ qL` for an arbitrary lattice is part of Q3; until then the
general defect **is** the cross-ratio.

`D ≡ 0` would say `q ↦ log Z(q²)` is a valuation — the algebraic
shadow of an Euler product, the resolution tower localizing over
the primes. For the towers formalized here it never is, unless
there is nothing to couple: the defect matrix vanishes identically
**iff** the modal sector is the only sector
(`defect_forall_eq_zero_iff`) — for a graph carrier, iff its
cohomology lattice `H¹(G;ℤ)` is trivial
(`towerDefect_forall_eq_zero_iff`). Wherever there is geometry, the
primes couple through it — and wherever the sign is proved, it is
negative.

## What is established

- **The cross-ratio law.** On the cohomology lattice `H¹(G;ℤ)` of
  any finite multigraph with its harmonic energy, the
  residue-complexity defect equals the analytic cross-ratio
  `[log Z(q²) + log Z(q′²)] − [log Z(gcd²) + log Z(lcm²)]` —
  squares of resolutions forced by quadratic energy
  (`crossRatio_law`). Here
  and below `Z(β)` abbreviates the carrier's class Boltzmann sum at
  inverse temperature `β`, base scale normalized to `1`; `θ(s)` is
  its rank-one case.
- **The coupling reading.** Chinese remainder on the tower: the
  `lcm`-resolution *is* the fiber product of the two coarser ones
  over their shared base (`h1ReductionCRT`) — arithmetic descent is
  exact, on every carrier. At rank one the failure of the measure
  to follow is priced exactly: divisibility events `q ∣ X` are
  honest Gibbs masses (`resProb_eq_event_mass`), minus the defect
  is the log of their conditional association ratio
  (`neg_defect_eq_log_assoc`), and the sign theorem says an
  incomparable pair is strictly positively associated given its
  shared constraint (`condProb_mul_lt_of_incomparable`; coprime
  unconditional form `resProb_mul_lt_of_coprime`).
- **The sign, rank one, closed.** `D_s(q,q′) < 0` at every
  incomparable pair and every scale, zero exactly on chains — the
  defect detects divisibility (`defect_neg_of_incomparable`,
  `defect_eq_zero_iff`), and residue complexity is a submodular
  rank function on the divisibility lattice, strictly off chains
  (`resComplexity_strictSubmodular`).
- **The sign, diagonal forms, every rank.** Orthogonal sums add
  defects, so every positive diagonal form inherits the rank-one
  sign in every rank ≥ 1: strictly negative off chains, zero on
  them (`diagDefect_neg_of_incomparable`, `diagDefect_eq_zero_iff`).
  The *formalized* frontier is failure of orthogonal
  diagonalization into rank-one summands, not rank.
- **The classification, through the partition tower.** The
  argument consumes only three fields — a distinguished zero-energy
  sector, strictly positive energy at every other sector, a
  summable Boltzmann weight — isolated as the abstract **partition
  tower** (`PartitionTower`), whose defect is the cross-ratio of
  scaled partition functions and whose classification is proved
  once at that level (`defect_forall_eq_zero_iff`): the defect
  vanishes identically iff the modal sector is the only sector. At
  saturation only the modal sector survives (`tendsto_Z_atTop`),
  so on any nontrivial tower
  the defect converges along the staircase `(n+1, n+2)` to
  `−log Z(1) < 0` and is eventually strictly negative
  (`tendsto_defect_succ`, `eventually_defect_neg`); and the
  sampled complexity is recovered from coprime entries of a
  single defect matrix,
  `D(m, km+1) − D(k+1, k+2) → log Z(m²)`
  (`tendsto_defect_row_sub_succ`; rank one:
  `tendsto_defect_recovery`). Instances:
  rank-one theta (`defect_eq_thetaTower_defect`), every graph
  carrier — where the cross-ratio law identifies the
  residue-complexity defect with the tower's
  (`towerDefect_eq_partitionTower_defect`,
  `towerDefect_forall_eq_zero_iff`) — and **every positive-definite
  lattice action** (`QuadLatticeAction.toPartitionTower`).
- **Spectral peeling, the first layer.** On a nontrivial tower
  summability forces a locally finite spectrum
  (`finite_energy_le`), so the least positive energy is attained
  (`leastEnergy_isLeast`), strictly positive (`leastEnergy_pos`),
  with finite positive multiplicity (`leastEnergyMult_pos`), and
  both are asymptotic observables of the partition function:
  `−log(Z(β) − 1)/β → λ₁` and `e^{β·λ₁}·(Z(β) − 1) → N₁`
  (`tendsto_neg_log_Z_sub_one_div`, `tendsto_exp_mul_Z_sub_one`;
  sampled along `β = m²` as `tendsto_leastEnergy_sample`,
  `tendsto_leastEnergyMult_sample`) — consuming exactly the data
  the recovery formula produces. The extracted layer subtracts:
  the **residual subtower** (`residual`) deletes the `λ₁` level,
  keeps the modal sector, inherits all three fields, and
  satisfies `Z_res(β) = Z(β) − N₁·e^{−β·λ₁}` for `β ≥ 1`
  (`residual_Z`); when the residual is itself nontrivial its
  least energy is strictly larger (`leastEnergy_lt_residual`) —
  each peel moves up the spectrum — and when it is trivial,
  peeling terminates. The peel sequence (`peel 0 = T` and
  `peel (n+1) = (peel n).residual` — `peel_zero`, `peel_succ`)
  telescopes,
  `Z_{peel n}(β) = Z(β) − Σ_{i<n} Nᵢ·e^{−β·λᵢ}` for `β ≥ 1`
  (`peel_Z`), and while the `n`-th peel is nontrivial its layer
  `(λₙ, Nₙ)` is a limit of expressions in the original `Z` and
  the previously extracted layers alone — along the recovery
  samples `β = m²` too, the fixed-matrix datum literally
  (`tendsto_peel_leastEnergy`, `tendsto_peel_leastEnergyMult`,
  their `_sample` forms, strictly increasing by
  `peel_leastEnergy_strictMono`). And the peeling exhausts:
  every nonmodal sector is eventually peeled
  (`exists_notMem_range_peelEmbed`), the residual tail vanishes,
  `Z_{peel n}(β) → 1` (`tendsto_peel_Z`), and the layers sum to
  the whole excess, `Σₙ Nₙ·e^{−β·λₙ} = Z(β) − 1` for `β ≥ 1`
  (`hasSum_peel_layers`): one fixed defect matrix determines the
  full spectrum with multiplicities, no tail escaping the
  enumeration. At carrier level, only the modal sector survives
  every peel: `⋂ₙ range(peelEmbed n) = {modal}`
  (`iInter_range_peelEmbed`).
- **The prime pairing, rank one.** `⟨p,q⟩ := −D` is strictly
  positive for distinct primes and saturates at the base complexity
  `log θ(s)` along coprime pairs at infinity (`pairing_pos`,
  `tendsto_pairing`); the tower-level coprime analogue is the
  staircase saturation `−D(n+1, n+2) → log Z(1)`
  (`tendsto_defect_succ`).
- **Rank two.** On the theta graph the cycle Gram inverts to the
  hexagonal form `(a² − ab + b²)/3`, and the defect is strictly
  negative at `(2,3)` (`thetaGraph_towerDefect_neg`), through the
  factorization `hexTheta s ≤ θ(s/3)·θ(s/4)`.
- **The kernel chambers, rank one.** Write `F(m) := log θ(m²s)`,
  `h_s(x) := log θ(s·e^{2x})`, `x_p := log p`. On distinct primes
  the pairing is the Hankel-cocycle second difference
  `⟨p,q⟩ = h_s(0) + h_s(x_p+x_q) − h_s(x_p) − h_s(x_q)` with true
  diagonal zero — `M = M̃ − diag(d_s(x_p))`, the diagonal
  corrections being the Q5 curvatures
  `d_s(x) = h_s(0) − 2h_s(x) + h_s(2x)`. On zero-sum weights the
  base and row/column terms cancel exactly
  (`quadFormOn_pairing_eq`); for every `s ≥ 1` the pairing is CND
  on every finite prime set at once (`pairing_cnd_large`,
  dimension-free), and no set of three or more primes stays CND
  as `s → 0` (`pairing_not_cnd_small`, through the dominance
  threshold `pairing_dominates_small`; the normalized small-scale
  asymptotic is `tendsto_exp_mul_pairing`). The saturation
  deficit `B := log θ(s)·J − M` has exact entries
  `F(p) + F(q) − F(pq)` off the diagonal and `F(1)` on it, is
  entrywise positive (`pairing_lt_base`), and satisfies
  `cᵀBc = −cᵀMc` on zero-sum weights
  (`quadFormOn_deficit_eq_neg`) — deficit-PSD implies CND
  (`deficit_psd_implies_cnd`), and only that: the converse fails
  at every scale `s ≥ 1` (`cnd_not_psd`). Both notions
  restrict to subsets (`IsCNDOn.subset`, `IsPSDOn.subset`), so
  enlarging the prime set only shrinks the valid-scale sets.
- **The star obstruction: no uniform deficit-PSD threshold.**
  At every scale `s > 0` some finite prime set has non-PSD
  saturation deficit (`deficit_not_psd`; the kernel `deficit`
  makes `B = log θ(s)·J − M` definitional): the deficit of
  `{2, q₁, …, qₙ}` with large satellites approaches the star
  matrix with diagonal `log θ(s)` and spokes `log θ(4s)`, and
  the explicit star weight has negative energy once
  `n > (log θ(s)/log θ(4s))²` — no eigenvalue machinery, only
  the geometric saturation bounds. So `sup_P s_PSD(P) = ∞`, and
  with `pairing_cnd_large` the converse CND ⇒ deficit-PSD fails
  at every scale `s ≥ 1` (`cnd_not_psd`), not merely at the
  numerical `s = 0.12` witness.
- **The refined log-convexity, rank one — Q5's base case,
  closed.** The Gibbs bridge `θ′(α) = −∑ k²·e^{−αk²}`,
  `θ″(α) = ∑ k⁴·e^{−αk²}` (`hasDerivAt_theta`,
  `hasDerivAt_thetaDeriv`); the functional equation
  `α·θ′(α)/θ(α) + (π²/α)·θ′(π²/α)/θ(π²/α) = −1/2`
  (`theta_logDeriv_dual`) with the fixed-point anchor
  `θ′(π) = −θ(π)/(4π)` (`thetaDeriv_pi`) — mean Gibbs energy
  exactly `1/(4π)` at the self-dual scale; the fluctuation
  inequality `α·Var(E) > ⟨E⟩` at `α ≥ π`
  (`theta_fluctuation_large`, `theta_logDeriv_numer_pos_large`);
  global strict monotonicity of `α·θ′(α)/θ(α)` by reflection
  through the functional equation
  (`theta_logDeriv_strictMonoOn`); and the strict rectangle and
  midpoint inequalities `θ(a²t)·θ(b²t) < θ(t)·θ((ab)²t)`,
  `θ(a²t)² < θ(t)·θ(a⁴t)` for every ratio above one
  (`theta_rect_strict`, `theta_sq_lt`) — dropping both the
  `2 ≤ a` and the `a < b` of `theta_prod_lt_general`. Under
  `θ(β) = θ₃(β/π)` this is the Faulhuber–Steinerberger refined
  log-convexity
  ([*Optimal Gabor frame bounds for separable lattices and
  estimates for Jacobi theta
  functions*](https://arxiv.org/abs/1601.02972), Theorems
  2.2–2.3; also [Faulhuber
  2020](https://arxiv.org/abs/1709.06006), Proposition 3.13):
  `u ↦ log θ(eᵘ)` is strictly convex.
- **Strict Q5 for diagonal forms, every rank.** The factored
  Boltzmann sum of a positive diagonal form satisfies the strict
  rectangle and midpoint inequalities for `r ≥ 1`, `t > 0` and
  every ratio above one (`diagTheta_rect_strict`,
  `diagTheta_sq_lt`) — rank-one Q5 lifted axis-by-axis, the same
  orthogonal-sum lift that carries Q1 (`diagDefect_eq_sum`). No
  positive diagonal form is a Q5 counterexample.

Why there is a sign at all: in the continuum limit the Gaussian
factors exactly and the defect vanishes with it. Everything here
lives in the Poisson-summation corrections the continuum forgets —
which is why the formalized rank-one all-scale proofs pass through
the Jacobi duality `θ(π²/α) = √(α/π)·θ(α)` before closing on
rational arithmetic. The classification needs less: modal
concentration at large resolution, no duality.

## The symmetry

The defect is a weight-zero combination. Each factor `log Z(q²s)`
carries modular weight — the duality multiplies `θ` by a
prefactor — but the cross-ratio weights its four terms
`½ + ½ − ½ − ½`, and the prefactors cancel exactly because
`gcd·lcm = q·q′`. What survives is an exact reflection law,

    D_s(q, q′) = D_{π²/(s·lcm²)}(q/g, q′/g),    g := gcd(q, q′).

Every pair reflects onto its coprime reduction at a dual scale. On
a coprime pair the involution fixes the pair and moves only the
scale, so each coprime entry is an even function of `log s` about
its own center `s* = π/(qq′)` — centers additively separable in
the log-primes. Both all-scale sign proofs originally re-derived
the reflection inline (`Sign`, branch two; `Submodular`,
reflection branch); the law is now stated once — the rectangle
engine and the arithmetic law (`theta_rect_dual`, `defect_dual`),
the coprime evenness (`defect_scale_even`) — and both branches
consume it through the inequality equivalence
(`theta_rect_lt_iff`).

The compact form: write `H(u) := log θ(eᵘ)`. Then
`H(u) + (u − log π)/4` is even about `u = log π`, and everything
here is a second difference of `H` — the defect its mixed second
difference on the log-divisibility lattice, Q4's diagonal
correction its equal-leg difference, Q5 its infinitesimal one, the
duality its reflection symmetry. At higher rank multivariate
Poisson summation gives the same cancellation with the dual
lattice (inverse Gram) appearing:
`D_{L,s}(q,q′) = D_{L*,π²/(s·lcm²)}(q/g, q′/g)` — the defect
field of `L` at scale `s` is the defect field of `L*` at
reflected scales. The higher-rank statement is the roadmap's
first formalization target.

## The questions

Second edition. The first edition mixed three strata — solved
mathematics, known mathematics awaiting formalization, and open
research — and completing the ladder separated them: closed
results live in **What is established** (formal theorems alongside
numerical counterexamples and explicit nonclaims),
known-but-unformalized implications in **The roadmap**, and this
section keeps only
statements whose truth is unknown. Numbering is stable across
editions — Q1–Q6 keep their subjects, Q7 splits off the tail of
the old Q6 — and every inverse question names the datum it
consumes. The organizing axes, learned by closing rank one: rank
one versus higher rank, scalar versus residue-refined data,
pairwise versus higher-order interaction.

- **Q1 — higher-rank strictness and equality.** The non-strict
  sign is known mathematics: Regev and Stephens-Davidowitz prove
  that two sublattices `M,N ⊆ L` are positively correlated under
  normalized Gaussian mass, `ρ(M)·ρ(N) ≤ ρ(L)·ρ(M ∩ N)`
  ([*An Inequality for Gaussians on Lattices*](https://doi.org/10.1137/15M1052226),
  Theorem 5.1), and applying this inside `gL` to `qL` and `q′L` —
  intersection `lcm(q,q′)L` — gives `D_L(q,q′) ≤ 0` for every
  lattice. Formalizing that implication is roadmap work, not a
  question. Open is what the correlation inequality cannot see:
  on a positive-rank lattice, is `D_L(q,q′) = 0` exactly when
  `q ∣ q′` or `q′ ∣ q`? Strict Q5 would answer outright — the
  defect is a rectangle of `H_L`, and strict convexity kills
  every nondegenerate rectangle — so Q1 is now downstream of the
  master conjecture. Independently: a generic residue tower on
  `L ⧸ qL` would make the correlation an intrinsic event
  statement and supply the general-lattice cross-ratio law.

- **Q2 — sparse spectral rigidity, by datum.** Put
  `F_s(m) := log Z(m²s)` for `m ≥ 1`. Four input regimes: the
  all-scale defect field; one fixed-`s` defect matrix; a single
  infinite prime row of that matrix; a finite entry set. The
  recovery formula

      F_s(m) = lim_{k→∞} ( D_s(m, km+1) − D_s(k+1, k+2) )

  consumes coprime entries of one fixed-`s` matrix along
  saturation and is a theorem in exactly this single-limit form
  (`tendsto_defect_row_sub_succ` at `PartitionTower` level,
  `tendsto_defect_recovery` at rank one); joint saturation
  recovers `F_s(1)`,
  and the row limit `lim ⟨p,q⟩_s = F_s(1) − F_s(p)` recovers
  `F_s(p)`. Three regimes are thereby settled or reduced: the
  all-scale field recovers `Z` at every scale — its kernel is
  exactly theta-equivalence, no longer a question; one fixed
  matrix recovers the sample sequence `(F_s(m))_{m≥1}`; and the
  samples determine the full spectrum by peeling, which is
  now fully proved (target 9 — established, spectral
  peeling):
  the all-one sample sequence identifies the modal-only tower,
  and on a nontrivial tower summability forces a locally finite
  positive spectrum, so
  `λ₁ = lim_m −log(Z(m²) − 1)/m²` and
  `N₁ = lim_m e^{λ₁m²}(Z(m²) − 1)` extract the least energy and
  its multiplicity, and the tower peels by subtraction and
  recursion. The genuinely open regimes are the sparse ones:
  does one infinite prime row already suffice? The finite-entry
  regime is underspecified without a model class — fix the rank
  and normalization before asking for minimal determining
  sets. The reflection law acts on the field, not on
  a fixed-`s` matrix — reflected scales vary with the pair, so a
  single matrix is untouched by duality while the field
  determines its own reflection. Field rigidity and matrix
  rigidity are different theorems; every statement names its
  datum.

- **Q3 — the residue-refined inverse problem.** Downstream of Q2
  in exposition, parallel in experiment. The datum: the
  coset-mass vectors on `L ⧸ qL` — the all-scale family or the
  family at one fixed scale `s`, each refining the corresponding
  Q2 scalar regime. Scalar data cannot see below
  theta-equivalence — the all-scale scalar field has exactly
  theta-equivalence as its kernel (Q2) — so the question is
  which refinement does, and at which datum: does the complete
  coset-mass family, its finite Fourier transform, or a smaller
  collection of characters determine the quadratic lattice up to
  isometry? For graph carriers, does the corresponding invariant
  determine graph isomorphism, cycle-matroid equivalence, or a
  coarser relation? The tower side is computable today —
  `h1ReductionCRT` and the residue actions are formalized — so
  small cospectral pairs can be tested before the scalar theory
  settles.

- **Q4 — phase geometry: Q4-CND and Q4-PSD.** Both asymptotic
  regimes of Q4-CND are theorems (established, the kernel
  chambers); the implication deficit-PSD ⟹ CND is proved
  (`deficit_psd_implies_cnd`), and the converse fails at every
  scale `s ≥ 1` (`cnd_not_psd`; first seen numerically at
  `s = 0.12` on five primes). The identity behind the
  implication localizes the difference
  (`quadFormOn_deficit_eq_neg`), as a dichotomy: a CND failure
  is itself a zero-sum deficit-PSD failure, while if CND holds
  and deficit-PSD fails, every negative direction has nonzero
  mean — the star obstruction's witness is such a direction.
  Open is the geometry
  of the middle, one clause per matrix. **Q4-CND**: for a finite prime set `P`, is the
  valid-scale set `{ s : pairing CND on P }` an upper interval?
  The controlling statistic is the largest eigenvalue of the
  pairing matrix restricted to the zero-sum subspace — CND holds
  iff it is `≤ 0` — and no symmetry forces a single crossing:
  the reflection evaluates each entry at its own pair-dependent
  dual scale and does not act on fixed-set chambers. With
  `s_c(P) := inf { s₀ : the pairing on P is CND for all s ≥ s₀ }`,
  the theorem gives `sup_P s_c(P) ≤ 1` (`pairing_cnd_large`);
  committed sweeps (`recon/data/q4_sweep_*.json`) place the
  crossings at `0.080 → 0.108 → 0.127 → 0.145 → 0.161` on the
  first 3–15 primes, decelerating well below the bound; the
  binding inequality `log θ(s) ≥ 2·log θ(4s)` crosses near
  `s = 0.196` — now identified as the `n = 4` star model,
  `√4 = 2` — and the first hundred primes are CND at
  `s = (log 2)/3`. The small-`s`
  theorem is the normalized limit `⟨p,q⟩ = 2e^{−σ}(1 + o(1))`
  with `σ = π²/(s·p²q²)` (`tendsto_exp_mul_pairing`); the
  quantitative `O(e^{−σ})` relative rate remains numerical,
  unformalized. **Q4-PSD**: the saturation
  deficit, controlled by its ordinary smallest eigenvalue, with
  committed crossings `0.085 → 0.169 → 0.280 → 0.385 → 0.484` on
  the same sampled sets. That growth cannot saturate: for fixed
  `s` the deficit of `{2, q₁, …, qₙ}` with large satellites
  tends to a star matrix with smallest eigenvalue
  `F(1) − √n·F(2)`, negative once `n > (F(1)/F(2))²`. With
  `s_PSD(P)` defined like `s_c(P)` for the deficit,
  `sup_P s_PSD(P) = ∞`: no uniform bound can hold, though each
  fixed finite set may still have a finite eventual-PSD bound —
  the star obstruction, now a theorem (`deficit_not_psd`). With
  `pairing_cnd_large` the converse CND ⇒ deficit-PSD fails at
  every scale `s ≥ 1` (`cnd_not_psd`), not merely at the
  `s = 0.12` witness.
  The rate is now measured (`recon/README.md`,
  `q4_star_rate.json`): star-set crossings agree with the
  limiting model `log θ(s) = √n·log θ(4s)` to displayed
  precision; the last sampled slope is `0.170 ≈ 1/6`, with the
  sampled offsets pre-asymptotic — the expansion predicts
  `s = (log n)/6 + n^{−1/6}/3 + O(n^{−1/3})`, an algebraic
  correction not yet small at these `n`; and the minimal
  eigenvector's geometry crosses over from near-zero-sum on
  small sets to star-like (squared mean projection `→ 1/2`) on
  large ones. Open here: intervality, and promoting the model
  agreement to explicit bounds. The first falsification
  hunt found one detected sign change per statistic on each
  sampled grid, brackets bisected (`recon/README.md`) —
  consistent with intervality, still unproven. The transform-realization question that
  used to close this entry now seeds Q7.

- **Q5 — higher-rank thermodynamic curvature: the master
  conjecture.** Rank one is closed (established, the refined
  log-convexity); the whole goal is now: for every
  positive-definite lattice `L` of positive rank — rank zero has
  constant `H`, convex but never strictly — is

      u ↦ H_L(u) := log Z_L(exp u)

  strictly convex — equivalently, does the coupling-weighted
  fluctuation beat the mean, `β²·Var_β(E) > β·⟨E⟩_β`? The
  continuum Gaussian has `⟨E⟩ = n/(2β)`, `Var = n/(2β²)`, so its
  curvature vanishes identically: the conjecture lives entirely
  in the Poisson corrections. The stakes are exact. Resolutions
  scale the form uniformly, so with `u = log s + 2·log g`,
  `x = 2·log(q/g)`, `y = 2·log(q′/g)`,

      D_L(q,q′) = [H_L(u+x) + H_L(u+y)] − [H_L(u) + H_L(u+x+y)],

  a rectangle of the single-variable `H_L` with far corner at
  `lcm` because `gcd·lcm = q·q′`: strict convexity gives
  `D_L < 0` off chains and `= 0` on them — **strict Q5 implies
  Q1 completely**, inequality and equality case at once, for
  arbitrary real ratios. It is strictly stronger than the known
  correlation theorem, so it is stress-tested numerically before
  any attempt at a formal proof. The first sweeps are on the
  record (`recon/`, rank two, det-1 binary moduli): no
  counterexample at any sampled point; along the shear ray
  toward degeneracy the sampled ratio falls
  `2.43 → 1.42 → 1.04 → 1.0003`, leaving a margin `r − 1` of
  only `2.8·10⁻⁴` at the deepest member — consistent with
  asymptotic sharpness; if that limiting picture is correct, no
  proof can rely on a uniform positive margin. The observed
  thin-tail behavior is consistent with the surviving correction
  being the rank-one fluctuation at large reflected coupling
  (`theta_fluctuation_large`'s regime). In rank two every det-1
  form is integrally isodual (`JᵀMJ = M⁻¹`), so genuinely
  distinct dual pairs first exist at rank 3 — and rank three is
  now on the record too (`recon/README.md`): cubic `ℤ³`
  reproduces the rank-one ratio exactly, the FCC/BCC pair — the
  first genuinely distinct dual pair — carries the program's
  largest sampled margin, and squashing FCC collapses the margin
  to `2.3·10⁻¹³` with the sampled minimum *leaving the duality
  center* and the two sides of the dual pair binding at
  different locations and magnitudes. No sampled point
  contradicts Q5. The shape of a possible failure is already
  constrained: at large coupling the shortest shell dominates and
  `β²Var − β⟨E⟩ ≈ βλ₁N₁e^{−βλ₁}(βλ₁ − 1) > 0` — the rank-one
  Fact-1 mechanism, universal; the duality
  `H_L″(u) = H_{L*}″(2·log π − u)` transports it to small
  coupling for `L*` — convexity for every lattice on `β ≥ π` is
  convexity everywhere, the class closed under duality, an
  individual profile self-symmetric when `L` and `L*` are
  theta-equivalent (isoduality sufficient, not necessary); and
  orthogonal sums inherit convexity from their summands — the
  diagonal case is a theorem (`diagTheta_rect_strict`) — so any
  counterexample yields an orthogonally indecomposable one. What
  survives is an intermediate window between the two proven
  tails — at the duality center `β = π` for the symmetric
  rank-two samples, but drifting off-center on one side of the
  pair once genuine dual asymmetry exists (the rank-3 squash
  record). The
  product `λ₁(L)·λ₁(L*)` remains a candidate coordinate for
  organizing this intermediate regime; the rank-two data
  establishes only a narrower numerical pattern — along the
  sampled thin subray the minimum sampled ratio falls
  monotonically with the product, while the product is not a
  single-valued predictor across the moduli space
  (`recon/README.md`). If strictness fails, the
  failure mode matters: curvature merely touching zero refutes
  strict universality without creating chambers; only a
  sign-changing counterexample makes Q5 the curvature analogue
  of Q4.

- **Q6 — higher mixed-difference chambers.** The correct
  algebraic object is the symmetric mixed-difference hierarchy of
  `K` on the prime-exponent lattice: `Δ_{p₁}⋯Δ_{p_k}K` measures
  `k`-prime coupling. The pairing matrix is this hierarchy's
  `k = 2` layer, and Q4's saturation deficit is its union form
  `F(p) + F(q) − F(pq)` off the diagonal: Q4's kernel geometry is
  the definiteness theory of the first nontrivial level (its
  identity layer is roadmap work, target 7).
  Numerical evidence in rank one indicates that the
  three-prime difference at `2,3,5` changes sign with the scale,
  so the expected structure is a system of sign chambers rather
  than a uniform alternating-sign law. Which asymptotic regimes
  and inequalities survive beyond pairwise correlation — what are
  the `k ≥ 3` analogues of the two proved Q4 regimes?

- **Q7 — realizability.** Split from the old Q6; either half is
  a program. Which abstract hierarchies actually come from
  lattices: which mixed Hessians, which kernels, which deficit
  remainders are realizable by lattice theta functions? Because
  `K` is an intersection surprisal rather than an entropy,
  entropic-cone membership is a separate representation problem.
  The concrete seed is the transform question inherited from Q4
  (with `F(m) := log θ(m²s)` as in the kernel chambers):
  saturated rows obstruct any Gram representation of `B/2` by
  Dirichlet monomials `p^{−λ}` against a shared measure — the
  row limit `B_pq → F(p)` as `q → ∞` depends on `p`, while
  `∫ p^{−λ}q^{−λ} dν → ν({0})` does not. Survival vectors
  `𝟙[t ≥ p]` in `L²(−dF)` split off a canonical PSD component
  with Gram kernel `F(max(p,q))`, but the remainder
  `F(min(p,q)) − F(pq)` (diagonal `F(1) − F(p)`) keeps the same
  `p`-dependent row limit: the obstruction survives the
  subtraction, and realizing the remainder is Q7's first
  target.

## The roadmap

Known mathematics awaiting formalization, and the reconnaissance
that decides where the frontier actually is. Every target names
its landing; these results stay useful whatever the experiments
say.

Formalization targets:

1. **Higher-rank defect duality.** Multivariate Poisson summation
   gives `D_{L,s}(q,q′) = D_{L*,π²/(s·lcm²)}(q/g, q′/g)` — the
   weight-zero cancellation of The symmetry with the dual lattice
   appearing. `theta_rect_dual` is the rank-one case and the
   template.
2. **Strict Q5 for positive diagonal forms** — done
   (`diagTheta_rect_strict`, `diagTheta_sq_lt`, lifted from
   `theta_rect_strict` by the `Theaetetus.Diagonal` pattern).
   What remains under this heading is the general orthogonal-sum
   reduction — any Q5 counterexample yields an orthogonally
   indecomposable one — which awaits a formal orthogonal sum of
   lattice actions.
3. **The Regev–Stephens-Davidowitz implication.** Sublattice
   correlation applied inside `gL` gives the non-strict
   `D_L(q,q′) ≤ 0` for every lattice — Q1's inequality half.
4. **The Q2 recovery formula** — done
   (`tendsto_defect_row_sub_succ` at `PartitionTower` level,
   instantiated at rank one as `tendsto_defect_recovery`), in the
   datum-honest form: a single limit of differences of entries of
   one fixed-scale defect matrix,
   `D_s(m, km+1) − D_s(k+1, k+2) → F_s(m)`.
5. **The certification chain** for higher-rank numerics: a lower
   bound `Q(x) ≥ μ‖x‖²` from the least Gram eigenvalue, shell
   counts, moment tails with the dimension-dependent polynomial
   factor, and interval linear algebra for extremal eigenvalues.
   `Theaetetus.Fluctuation`'s geometric-domination bounds are the
   rank-one shapes. The first link is in place
   (`Theaetetus.Certification`): `μ` is a coercivity constant for
   a Gram form — `μ·∑xᵢ² ≤ xᵀQx` — iff it lower-bounds every
   eigenvalue (`Matrix.IsHermitian.mul_sum_sq_le_quadForm`,
   `Matrix.IsHermitian.le_eigenvalues_of_mul_sum_sq_le`, packaged
   as `Matrix.IsHermitian.mul_sum_sq_le_quadForm_iff`), while row
   dominance `μ + ∑_{j≠i}|Qᵢⱼ| ≤ Qᵢᵢ` — finitely many entrywise
   inequalities, rational arithmetic when the entries are
   rational — certifies the same bound, positive definiteness,
   and a spectrum-wide `μ ≤ λ`
   (`mul_sum_sq_le_quadForm_of_dominant`, `posDef_of_dominant`,
   `le_eigenvalues_of_dominant`), transferring to lattice energies
   through `QuadraticAction.mul_sum_sq_le_energy`. Shell counts,
   moment tails, and the interval crossing algebra remain.
   Certified this way, a reconnaissance sign is a certificate —
   and a counterexample arrives pre-packaged for its own
   formalization.
6. **`Theaetetus/Status.lean`** — done: the statement-level
   manifest exists — every claim this document makes of the
   tree, restated as an `example` discharged by the theorem it
   cites, so statement drift fails `lake build`. The companion
   docstring sweep is also done: no Lean docstring or comment
   references a prose coordinate (the one-way rule, now in
   `CLAUDE.md`).
7. **Q6's identity layer.** Rectangle identities and the
   characterization of vanishing cross-prime differences for the
   mixed-difference hierarchy `Δ_{p₁}⋯Δ_{p_k}K`.
8. **The star obstruction** — done (`deficit_not_psd`,
   `cnd_not_psd` in `Theaetetus.StarObstruction`): the explicit
   star-weight witness closed it without eigenvalue machinery.
   What remains under this heading is the rate, which stays on
   the frontier (Q4-PSD).
9. **Spectral peeling** — done (`Theaetetus.Peeling`): local
   finiteness, attainment, both extraction limits with sampled
   forms, the residual subtower with its bridge, strict
   progress, the telescoped peel sequence, every layer as a
   limit of the original data alone, and exhaustion — the
   composite carrier embedding (`peelEmbed`) eventually excludes
   every nonmodal sector (`exists_notMem_range_peelEmbed`), so
   the residual tail vanishes (`tendsto_peel_Z`) and the layers
   sum to the whole excess, `Σₙ Nₙ·e^{−β·λₙ} = Z(β) − 1` for
   `β ≥ 1` (`hasSum_peel_layers`, `tsum_peel_layers`). One fixed
   defect matrix determines the full spectrum with
   multiplicities.

Reconnaissance, falsify-first:

1. **Higher-rank Q5.** Normalize every Gram matrix to determinant
   one before profiling: the repo's hexagonal form
   `(a² − ab + b²)/3` has determinant `1/12` with `M⁻¹ ≅ 12M`, so
   it is self-similar under duality with reflection center
   `β* = π·√12`, not `π` — the `√12`-rescaling is the genuinely
   isodual normalization. Test dual pairs together on the
   half-profile `u ≥ log π` only: the reflection makes
   `[π, ∞) × {L, L*}` a complete search domain. Sweep whole
   half-profiles, never the center alone — an isodual profile
   constrains a failure window to be symmetric, not absent. Start
   at the normalized hexagonal form, then the binary shear family
   toward degeneracy; record `λ₁(L)·λ₁(L*)` per form as a
   candidate degeneration coordinate. First runs committed (`recon/data`:
   baselines, the unit-circle arc, the shear ray with its fine
   scan; findings in `recon/README.md`). Ternary runs committed
   as well — rank-3 baselines, the cubic→FCC path, the FCC
   squash family with two fine scans; under genuine dual
   asymmetry the sampled minimum leaves the duality center.
   Next: certified tails (target 5) to harden the
   deep-degeneration margins.
2. **Q4 phase geometry** — first uncertified sweep complete
   (`recon/q4.py`; `q4_sweep_*.json`, `q4_witness.json`;
   findings in `recon/README.md`): correctly-oriented extremal
   eigenvalues, one detected sign change per statistic per
   sampled grid with brackets bisected, and the historically
   cited transitions and `s = 0.12` witness reproduced from
   committed code. Next: certified entry intervals and interval
   linear algebra for the crossings (target 5), harder
   intervality falsification, and the star-obstruction rate
   against its `s_PSD ~ (1/6)·log n` benchmark.

The sequence so far: the restructuring, strict Q5 for diagonal
forms, the dual-aware harness, the rank-two and rank-three
sweeps, the first Q4 sweep, the star-obstruction theorem, the
manifest with its docstring sweep, the recovery formula, and
spectral peeling are complete. Still open: higher-rank duality
(target 1), the Regev–Stephens-Davidowitz implication
(target 3), the certification chain (target 5) — the one both
reconnaissance lanes name as their next step — and Q6's
identity layer (target 7). The verdicts to date:
Q5 stays a universal conjecture, with margins vanishing toward
every degenerate boundary probed and its binding point leaving
the duality center under dual asymmetry; Q4's uniform-PSD
question is resolved negatively by the star obstruction, leaving
the rate and intervality open.

## The ladder

The first edition's program — the formalization order for the
symmetry and its consequences, kept as the record of how rank one
closed. All seven rungs are complete — the reflection law in
`Theaetetus.Duality` (with the corollary `theta_rect_lt_iff`,
which both sign proofs' reflection branches now consume), coarse
Q5 in `Theaetetus.Midpoint`, both Q4 chambers
(`Theaetetus.SmallScale`, `Theaetetus.Flattening`) through the
kernel interface (`Theaetetus.Kernel`) and the normalized
asymptotics (`Theaetetus.LargeScale`), and the
Faulhuber–Steinerberger port across `Theaetetus.Gibbs`,
`Theaetetus.FunctionalEquation`, `Theaetetus.Fluctuation`, and
`Theaetetus.LogConvexity`:

1. `theta_rect_dual` — the real-variable reflection engine: for
   `t, a, b > 0` the cross-ratio
   `θ(a²t)·θ(b²t) / (θ(t)·θ((ab)²t))` is invariant under
   `t ↦ π²/((ab)²t)`. Replaces both inline reflections.
2. `defect_dual` — the arithmetic corollary:
   `D_s(q,q′) = D_{π²/(s·lcm²)}(q/g, q′/g)`.
3. `defect_scale_even` — coprime entries even in `log s` about
   `s* = π/(qq′)`.
4. Coarse Q5 — `θ(a²t)² ≤ θ(t)·θ(a⁴t)` for real `a ≥ 2`, the
   `b → a` limit of `theta_prod_lt_general`; nonnegativity of
   every Q4 diagonal correction.
5. The large-scale chamber — for every `s ≥ 1` the prime pairing
   is CND on every finite prime set at once
   (`pairing_cnd_large`), dimension-free through the exact
   identity `quadFormOn_pairing_eq`.
6. The small-scale chamber — every set of three or more primes
   fails CND for all sufficiently small `s`
   (`pairing_not_cnd_small`).
7. The refined log-convexity — the four-round
   Faulhuber–Steinerberger port: the Gibbs bridge
   `θ′(α) = −∑ k²·e^{−αk²}`, `θ″(α) = ∑ k⁴·e^{−αk²}`
   (`hasDerivAt_theta`, `hasDerivAt_thetaDeriv`); Fact 2, the
   functional equation
   `α·θ′(α)/θ(α) + (π²/α)·θ′(π²/α)/θ(π²/α) = −1/2`
   (`theta_logDeriv_dual`), with the fixed-point anchor
   `thetaDeriv_pi`; Fact 1, the large-coupling fluctuation
   inequality `α·Var(E) > ⟨E⟩` (`theta_fluctuation_large`,
   `theta_logDeriv_numer_pos_large`); and the assembly — global
   strict monotonicity by reflection
   (`theta_logDeriv_strictMonoOn`), the strict rectangle
   inequality `theta_rect_strict` for `1 < a, b`, and the strict
   midpoint `theta_sq_lt`. Q5 closed at rank one; the genuinely
   open core is higher rank.

## The map

The root module [`Theaetetus.lean`](Theaetetus.lean) imports every
module under a one-line section comment, in logical order from the
analytic primitive to the rank-two witness. That import list is the
table of contents: it compiles, so it cannot drift. Each module's
docstring carries its local story, in mathematics and Lean names
only — and `Theaetetus/Status.lean` is the manifest: every claim
this document makes of the tree, restated as an `example` and
discharged by the theorem it cites, so a renamed theorem, a
weakened statement, or an unwitnessed claim fails the build.

## Building

    nix develop -c lake build        # or: nu tasks.nu check

Toolchain `leanprover/lean4:v4.26.0`, Mathlib pinned at `v4.26.0`.
Zero `sorry`, zero `axiom` declarations; `lake build` green is the
only definition of done. Where a desired statement fails, the
counterexample becomes a theorem. Version control is jujutsu.

## History

Built in eight milestones, `M0`–`M7`: scaffold; the scalar core and chain-vanishing; the
witness `θ(4/3)·θ(3) < θ(1/3)·θ(12)`; the sign at `(2,3)` for all
scales; the carrier — graph homology, the residue tower, the
cross-ratio law, the rank-two witness; outward — Q1 closed at rank
one, the pairing, the rank function, the kernel on `C₃`; the
reconciliation — the defect as conditional association, the sign
for diagonal forms in every rank, the zero-defect classification
for every carrier;
the interface — the partition tower, the classification proved once
abstractly, with rank one, every graph carrier, and every
positive-definite lattice action as instances.
