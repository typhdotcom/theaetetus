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
- **The sign, every lattice, non-strict.** The shifted-mass parity
  decomposition turns products of Gaussian masses into inner
  products of finite positive feature vectors
  (`gramMass_mul_eq_inner`, `sum_sq_parityVector`).
  Cauchy–Schwarz, AM–GM, residue dilation and coprime reduction then
  give `D_L(q,q′) ≤ 0` for every positive-definite lattice action
  (`gramDefect_nonpos`, `QuadLatticeAction.defect_nonpos`) — the
  Regev–Stephens-Davidowitz correlation theorem ported through to
  the defect.
- **The strict sign, diagonal forms, every rank.** Orthogonal sums add
  defects, so every positive diagonal form inherits the rank-one
  sign in every rank ≥ 1: strictly negative off chains, zero on
  them (`diagDefect_neg_of_incomparable`, `diagDefect_eq_zero_iff`).
  What remains unformalized is failure of orthogonal
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
reflected scales. This is now intrinsic, not merely a Gram-chart
calculation (`QuadLatticeAction.defect_dual`, through
`gramDefect_dual` and the weight-annihilation law
`fieldDefect_dual_of_log_reflect`).

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
  lattice. That implication is now formalized:
  `QuadLatticeAction.defect_nonpos`. Open is the equality
  classification: on a positive-rank lattice, is `D_L(q,q′) = 0`
  exactly when `q ∣ q′` or `q′ ∣ q`? Two routes are now visible.
  Strict Q5 would answer outright — the defect is a rectangle of
  `H_L`, and strict convexity kills every nondegenerate
  rectangle — so Q1 is downstream of the master conjecture. And
  the formalized correlation proof exposes an equality chain of
  its own: zero defect forces simultaneous saturation of the
  parity-vector Cauchy–Schwarz (collinearity), the AM–GM
  equality, and every residue-class inequality — a route to the
  classification independent of higher-rank Q5 (target 10), whose
  two analytic links are now characterized
  (`gramMass_sq_mul_sq_eq_iff`, `gramMass_mul_eq_avg_iff`).
  The scope matters: the conjecture concerns the scalar dilation
  chain `q ↦ qL`. On the full modular lattice of sublattices,
  incomparable pairs can have zero defect through an orthogonal
  splitting; the index-two diamond of target 7 is the calibration
  example (`defect_evenFst_evenSnd`). Thus the equality chain must
  rule that mechanism out for nontrivial coprime scalar dilations,
  not prove a false statement about arbitrary sublattices.
  Independently, a generic residue tower on `L ⧸ qL` would make the
  correlation an intrinsic event statement and supply the
  general-lattice cross-ratio law.

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
  used to close this entry now seeds Q7. A second geometry is now
  visible as well: the join kernel of `q ↦ -log Z(q²s)` is the
  resolution distance in target 11, and on coprime primes the
  pairing is a difference of two of its distances.

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

- **Q6 — higher interaction and the carrier boundary.** Raw mixed
  differences `Δ_{p₁}⋯Δ_{p_k}K` are not order-separated:
  degenerate cubes retain lower-order field data. Their observed
  sign changes therefore do not define new interaction chambers.
  The corrected object is the inclusion–exclusion defect `D_k`,
  which removes the lower-order faces. The abstract calculus is
  already formalized in the sibling project **Descent**. On a
  distributive lattice `D₃` decomposes into pairwise defects at
  derived squares (`defect3_decompose`) and the order-three gauge
  equals the pairwise gauge (`gauge3_eq_gauge`); on every lattice,
  observation at all finite orders adds nothing beyond orders two
  and three (`gaugeFam_eq_gauge3`). Since the divisibility lattice
  is distributive, its corrected hierarchy contains no
  irreducible higher-order datum. At pairwise-coprime resolutions
  the recurrence telescopes to

      D_k(q₁,…,q_k) = Σ_{j=1}^{k−1} D(q_j, q_{j+1}⋯q_k),

  proved for the log-partition field of any `Z` at any scale
  (`defectFam_logField_eq_telescope`): coprimality collapses the
  meet-translated subfamily of Descent's exact recurrence to the
  trivial resolution and annihilates its distributivity-gap
  remainder, and the join of a coprime family is its product
  (`supFam_of_pairwiseCoprime`). Eliminating from the front prices
  each entry against the product of those following it, but the
  total does not depend on that order: the telescope computes the
  symmetric abstract defect, so any two presentations of the same
  coprime family agree (`telescope_eq_of_perm`). At arity three
  this is the coherence identity

      D(a,b) + D(ab,c) = D(b,c) + D(a,bc),

  which is why prefix and suffix decompositions give the same sum.
  Composed with the two sign laws
  this makes every corrected order strictly negative at rank one
  for nontrivial coprime families (`defectFam_theta_neg`) and
  nonpositive for every positive-definite lattice action
  (`QuadLatticeAction.defectFam_nonpos`). The telescope
  reorganizes the corrected defects into pairwise ones; it does
  not make them vanish, and raw mixed differences remain a
  different object.

  How different is now exact. On a pairwise coprime triple the raw
  order-three cube at the trivial resolution is

      raw(a,b,c) = D(a,c) + D(b,c) − D(a·b,c)

  (`mixedDiff_triple_of_pairwiseCoprime`): the raw cube is its
  three pairwise faces minus the corrected defect, the corrected
  defect is itself pairwise on this distributive carrier, the
  meet-derived term `D(a ⊓ c, b ⊓ c)` collapses to `D(1,1) = 0`,
  and the shared face `D(a,b)` cancels. At `2,3,5` this reads

      raw(2,3,5) = D(2,5) + D(3,5) − D(6,5)

  (`mixedDiff_two_three_five`). The old `2,3,5` chamber is thereby
  a balance among three strictly negative rank-one pairwise
  defects — its sign is undetermined because the raw quantity
  subtracts `D(6,5)` — and not a new three-body phase. The
  corrected observable over the same triple has a determined sign:
  strictly negative at every positive scale
  (`defect3_theta_235_neg`). Neither statement makes any pairwise
  defect vanish.

  Genuine irreducible higher interaction moves to the carrier,
  and the Gaussian geometry there is now on the record. In the
  modular, non-distributive lattice of subgroups of `ℤ²` the five
  sublattices `2ℤ² ≤ {a even}, {b even}, {a+b even} ≤ ℤ²` realize
  the diamond faithfully, each priced by the logarithm of its own
  Gaussian mass. The pairwise data is nonpositive: the two
  coordinate sublattices split orthogonally and have zero defect,
  and each of them against the checkerboard has the strict
  midpoint defect `2·log θ(2s) − log θ(s) − log θ(4s)`. The
  order-three defect is nevertheless strictly positive — the
  exact recurrence kills all three pairwise terms and leaves the
  field gap across the distributivity-defect interval
  `[2ℤ², {a+b even}]`:

      D₃ = log ρ({a+b even}) − log ρ(2ℤ²) = 2·log(θ(2s)/θ(4s)) > 0

  (`defect3_diamond`, `defect3_diamond_eq`, `defect3_diamond_pos`
  in `Theaetetus.SublatticeDiamond`), tending to `log 2`, the
  logarithm of the index of the doubled lattice inside the
  checkerboard, as the scale falls to zero
  (`tendsto_defect3_diamond`).
  So off distributivity `D₃` does not descend to pairwise data,
  while the hierarchy stays observationally capped at order three.
  Every pairwise observation on that five-point carrier is
  nonpositive (`defect_diamondHom_nonpos`); the positive
  order-three one is the formal contrast.

  The boundary value being an index is the suggestive part, and
  what follows is a conjecture, not a theorem. For full-rank
  finite-index sublattices `A, B, C`, put `U = (A+B) ∩ C` and
  `V = (A∩C) + (B∩C)` — the two ends of the distributivity-defect
  interval. Then

      D₃,s(A,B,C) → log [U : V]   as   s → 0⁺.

  The proposed mechanism is one sentence: at the boundary the
  pairwise terms tend to zero by multiplicativity of covolume in
  the Gaussian mass, while `defect3_recurrence` leaves exactly the
  Gaussian mass gap from `V` to `U`, whose ratio is the index. The
  proved diamond is the first nontrivial case, `[U : V] = 2`
  (`relIndex_evenBoth_evenSum`, `tendsto_defect3_diamond_index`);
  the general statement is target 12. What remains beyond it is
  the equality mechanisms and the interaction of this order-three
  observable with lattice duality — a sharply bounded research
  problem rather than an unending tower of new couplings.

- **Q7 — realizability.** Split from the old Q6; either half is
  a program. Which abstract hierarchies actually come from
  lattices: which mixed Hessians, which kernels, which deficit
  remainders are realizable by lattice theta functions? Because
  `K` is an intersection surprisal rather than an entropy,
  entropic-cone membership is a separate representation problem.
  The datum must be named carefully. The image question for defect
  data — whether *some* theta field realizes a proposed observable
  — is well-posed. Recovering or rejecting a particular field
  representative from its defect alone is not: valuation shifts
  are invisible to the defect, and Descent already has
  defect-equivalent arithmetic fields with different realization
  status (`exists_defectEquiv_realizable_not_realizable`). Any
  field-level criterion must therefore fix a representative; the
  theta class supplies the canonical saturation normalization
  `K(q) → 0` as `q → ∞`.
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
that decides where the open questions actually lie. Every target
names
its landing; these results stay useful whatever the experiments
say.

The abstract lattice calculus belongs to **Descent**; Theaetetus
owns its Gaussian and arithmetic realization. Reuse across that
boundary should be an ordinary Lake dependency pinned to an
immutable revision, with a narrow imported surface and a local
bridge module. A mutable sibling-path dependency would make builds
checkout-dependent, while copying the hierarchy would create two
sources of truth. That boundary has landed: Descent is a Lake
dependency pinned to an immutable revision, and the bridge module
`Theaetetus.HigherInteraction` identifies the four-term
`fieldDefect` of any partition field with `Descent.defect` of its
fixed-scale logarithmic context field on the carrier of positive
naturals under divisibility (`fieldDefect_eq_defect`); the same
imported surface carries `Theaetetus.SublatticeDiamond` on the
subgroup lattice of `ℤ²`. The abstract hierarchy is consumed,
never forked. The dependency is
passive as well as one-way: Theaetetus does not schedule changes in
Descent, advance its roadmap, or require its active development to
accommodate this project. Adapter lemmas and application-specific
corollaries live here against the pinned release. A result that may
belong upstream is recorded only as a **Consider upstreaming to
Descent** note; Descent's own team decides whether and when to
harvest it, and Theaetetus continues without waiting.

Formalization targets:

1. **Higher-rank defect duality** — done. The defect construction
   applies to any partition field (`fieldDefect`), with the
   scalar, tower, and Gram defects as instances
   (`defect_eq_fieldDefect`,
   `PartitionTower.defect_eq_fieldDefect`,
   `gramDefect_eq_fieldDefect`), and the law the four-term
   alternating sum obeys is isolated once: **the defect
   annihilates affine log weights**
   (`fieldDefect_dual_of_log_reflect`) — the constant by sign
   count zero, the log-linear part by `gcd·lcm = q·q′`. The
   structural laws are generic too — symmetry, vanishing on
   chains, vanishing on the diagonal (`fieldDefect_comm`,
   `fieldDefect_eq_zero_of_dvd`, `fieldDefect_self`) — and the
   scalar and tower instances inherit them rather than reprove
   them. The Gram
   chart engine (`Theaetetus.GramDuality`): the Boltzmann sum of
   a positive-definite Gram form reflects through the dual Gram,
   `gramTheta M⁻¹(π²/α) = (α/π)^(d/2)·det(M)^(1/2)·gramTheta M α`
   (`gramTheta_dual`, from the Gaussian Poisson summation of
   `Theaetetus.Periodization`) — an affine log weight, so the
   Gram defect reflects with no weight at all
   (`gramDefect_dual`), only the coupling moving at coprime
   resolutions (`gramDefect_dual_coprime`); at rank one with unit
   Gram this is the scalar theory (`gramTheta_one_eq_theta`,
   `gramDefect_one_eq_defect`), `defect_dual` the rank-one case
   and `theta_rect_dual` the multiplicative engine beneath it.
   The intrinsic lift (`Theaetetus.LatticeDuality`): every Gram
   chart computes the basis-free partition function
   (`QuadLatticeAction.scaledPartFn_eq_gramTheta`), so two
   integral bases produce the same Gram defect
   (`QuadLatticeAction.gramDefect_gram_eq`), the intrinsic defect
   (`QuadLatticeAction.defect`) is chart-computed
   (`QuadLatticeAction.defect_eq_gramDefect`) and at unit scale
   is the tower defect
   (`QuadLatticeAction.toPartitionTower_defect`); the dual
   lattice is intrinsic — the `ℤ`-dual module with the
   inverse-Gram pairing (`QuadLatticeAction.dual`), whose chart
   at the dual basis of *every* integral basis is the inverse
   Gram (`QuadLatticeAction.dual_gram_at`, with
   `QuadLatticeAction.dual_gram` the chosen-chart instance), so
   the basis hidden in the construction does not matter — and the
   duality lands on `L` and `L*`:
   `QuadLatticeAction.defect_dual`.
2. **Strict Q5 for positive diagonal forms** — done
   (`diagTheta_rect_strict`, `diagTheta_sq_lt`, lifted from
   `theta_rect_strict` by the `Theaetetus.Diagonal` pattern), and
   the orthogonal-sum reduction with it
   (`Theaetetus.OrthogonalSum`): the orthogonal sum of two
   lattice actions (`QuadLatticeAction.orthSum`) multiplies
   partition functions (`QuadLatticeAction.orthSum_scaledPartFn`,
   with positivity `QuadLatticeAction.scaledPartFn_pos`), adds
   defects (`QuadLatticeAction.orthSum_defect`, through the
   generic laws `fieldDefect_congr` and `fieldDefect_mul`), and —
   because every factor's defect is nonpositive — vanishes iff
   every factor's defect vanishes
   (`QuadLatticeAction.orthSum_defect_eq_zero_iff`): any
   zero-defect witness descends past every orthogonal
   decomposition. At real scale the strict rectangle inequality
   is preserved by orthogonal sums
   (`QuadLatticeAction.orthSum_rect_strict`), so any failure of
   Q5 strictness descends to a factor
   (`QuadLatticeAction.rect_strict_descend`) — the promised
   counterexample reduction.
3. **The Regev–Stephens-Davidowitz implication** — done. The
   substrate (`Theaetetus.ShiftedMass`): the shifted Gaussian
   mass `gramMass M α x = ∑_{k∈ℤᵈ} e^{−α·Q(x+k)}`, its residue
   decomposition mod `n` (`gramMass_coset`), and the parity
   transport of a product — the parallelogram law splits the
   Gaussian, parity splits the image (`gramMass_mul_gramMass`).
   The geometry (`Theaetetus.Correlation`): the **parity feature
   vector** (`parityVector`) with its two identities — a product
   of masses is an inner product of feature vectors
   (`gramMass_mul_eq_inner`), and a squared norm is a mass
   product (`sum_sq_parityVector`) — so Cauchy–Schwarz gives the
   correlation inequality `m(x)²·m(y)² ≤ m(0)²·m(x+y)·m(x−y)`
   (`gramMass_sq_mul_sq_le`), its averaged form
   (`gramMass_mul_le_avg`), monotonicity under scalar dilation
   (`gramMass_dilate_mul_le`), and positive correlation at
   coprime dilations (`gramMass_coprime_mul_le`). With the
   coprime reduction of the field defect
   (`fieldDefect_div_gcd`), the sign lands: the defect is
   nonpositive for every positive-definite Gram form
   (`gramDefect_nonpos`) and every lattice action
   (`QuadLatticeAction.defect_nonpos`) — Q1's inequality half,
   at every rank. The defect is logarithmic correlation slack
   whose sign is controlled by the parity-vector Cauchy–Schwarz
   geometry; equality demands simultaneous saturation —
   collinearity of the feature vectors, the AM–GM equality, and
   every residue-class inequality in the chain.
4. **The Q2 recovery formula** — done
   (`tendsto_defect_row_sub_succ` at `PartitionTower` level,
   instantiated at rank one as `tendsto_defect_recovery`), in the
   datum-honest form: a single limit of differences of entries of
   one fixed-scale defect matrix,
   `D_s(m, km+1) − D_s(k+1, k+2) → F_s(m)`.
5. **The certification chain** for higher-rank numerics — done:
   coercivity, tails, moments, shell counts, and two-sided
   spectral bounds, all reduced to finitely many checkable
   inequalities. `Theaetetus.Fluctuation`'s geometric-domination
   bounds were the rank-one shapes. Coercivity
   (`Theaetetus.Certification`): `μ` is a coercivity constant for
   a Gram form — `μ·∑xᵢ² ≤ xᵀQx` — iff it lower-bounds every
   eigenvalue (`Matrix.IsHermitian.mul_sum_sq_le_quadForm`,
   `Matrix.IsHermitian.le_eigenvalues_of_mul_sum_sq_le`,
   `Matrix.IsHermitian.mul_sum_sq_le_quadForm_iff`), and the same
   holds above (`Matrix.IsHermitian.quadForm_le_mul_sum_sq`,
   `Matrix.IsHermitian.eigenvalues_le_of_quadForm_le`,
   `Matrix.IsHermitian.quadForm_le_mul_sum_sq_iff`); row dominance
   `μ + ∑_{j≠i}|Qᵢⱼ| ≤ Qᵢᵢ` — finitely many entrywise
   inequalities, rational arithmetic when the entries are
   rational — certifies the lower bound, positive definiteness,
   and a spectrum-wide `μ ≤ λ`
   (`mul_sum_sq_le_quadForm_of_dominant`, `posDef_of_dominant`,
   `le_eigenvalues_of_dominant`), dominance from above caps the
   spectrum (`quadForm_le_mul_sum_sq_of_dominant`,
   `eigenvalues_le_of_dominant`), and a single form evaluation at
   a concrete vector drives an eigenvalue out of a half-line in
   either direction (`Matrix.IsHermitian.exists_eigenvalues_lt`,
   `Matrix.IsHermitian.exists_lt_eigenvalues`) — the interval
   algebra for extremal eigenvalues. Coercivity transfers to
   lattice energies (`QuadraticAction.mul_sum_sq_le_energy`).
   Tails (`Theaetetus.Tails`): the lattice sum of a product weight
   factorizes exactly (`QuadraticAction.tsum_finPi_prod`), the
   scalar tail beyond radius `N` is geometrically dominated
   (`theta_tail_le`), any energy dominating `ν·∑kᵢ²` has its
   Boltzmann sum outside the sup-norm box bounded by
   `r·θ(ν)^{r−1}` copies of the scalar tail (`tail_exp_le`,
   instantiated as `QuadraticAction.tail_le`), the partition
   function splits into a finite box plus a certified truncation
   error (`QuadraticAction.partFn_le_box_add_tail`, packaged as
   the enclosure `QuadraticAction.partFn_mem_box_Icc`), and
   polynomial energy weights absorb at half coupling —
   `xᵐ·e^{−x} ≤ 2ᵐ·m!·e^{−x/2}` — so every energy-moment tail is
   the plain tail at `μ/2` with the factorial constant
   (`QuadraticAction.moment_tail_le`). Shell counts
   (`Theaetetus.Shells`): coercivity confines energy sublevels to
   boxes (`QuadraticAction.abs_le_of_energy_le`), so they are
   finite (`QuadraticAction.finite_energy_sublevel`) with at most
   `(2N+1)^r` sectors once `R < μ(N+1)²`
   (`QuadraticAction.energy_sublevel_ncard_le`), and every energy
   shell obeys the same bound
   (`QuadraticAction.energy_shell_ncard_le`). Certified this way,
   a reconnaissance sign is a certificate — and a counterexample
   arrives pre-packaged for its own formalization.
6. **`Theaetetus/Status.lean`** — done: the statement-level
   manifest exists — every claim this document makes of the
   tree, restated as an `example` discharged by the theorem it
   cites, so statement drift fails `lake build`. The companion
   docstring sweep is also done: no Lean docstring or comment
   references a prose coordinate (the one-way rule, now in
   `CLAUDE.md`).
7. **The higher-interaction bridge** — done. Descent remains the
   source of truth for the order-separated hierarchy: `defect3`,
   `defectFam`, the raw-cube isolation identity
   (`mixedDiff_triple_inf`), distributive decomposition
   (`defect3_decompose`, `gauge3_eq_gauge`), and universal
   saturation (`gaugeFam_eq_gauge3`). The Theaetetus landing is a
   thin bridge, not a reimplementation:

   - identify its positive-natural `fieldDefect` with Descent's
     pairwise defect on the arithmetic carrier — done
     (`fieldDefect_eq_defect` in `Theaetetus.HigherInteraction`,
     through the logarithmic context field `logField`);
   - prove the pairwise-coprime family telescope and compose it with
     `defect_neg_of_incomparable` and
     `QuadLatticeAction.defect_nonpos`, giving the strict rank-one
     and non-strict all-lattice sign laws for every corrected order
     — done (`defectFam_logField_eq_telescope`, through the peeling
     step `defectFam_cons_coprime` and the coprime join
     `supFam_of_pairwiseCoprime`, with elimination order immaterial
     by `telescope_eq_of_perm`; signs in `defectFam_theta_neg` and
     `QuadLatticeAction.defectFam_nonpos`);
   - isolate the raw `2,3,5` mixed difference as a combination of
     pairwise entries, explaining its sign change without promoting
     it to a new observable — done
     (`mixedDiff_triple_of_pairwiseCoprime` generically,
     `mixedDiff_two_three_five` at the observed triple, against the
     corrected sign `defect3_theta_235_neg`);
   - formalize the canonical `M₃` witness from the three index-two
     sublattices of `ℤ²` — done (`Theaetetus.SublatticeDiamond`).
     The five sublattices `2ℤ² ≤ {a even}, {b even}, {a+b even} ≤
     ℤ²` realize the diamond faithfully in the subgroup lattice of
     `ℤ²` (`diamondHom`, `diamondSub_injective`), with distinct
     atoms meeting at `2ℤ²` and joining to `ℤ²`. Each is priced by
     its own convergent Gaussian mass (`latMass`, `latMass_pos`),
     and the table is exact — `ρ(ℤ²) = θ(s)²`, `ρ(2ℤ²) = θ(4s)²`,
     `ρ({a even}) = ρ({b even}) = θ(s)·θ(4s)`,
     `ρ({a+b even}) = θ(2s)²` (`latMass_top`, `latMass_evenBoth`,
     `latMass_evenFst`, `latMass_evenSnd`, `latMass_evenSum`, the
     last through the parity rotation `(u,v) ↦ (u+v, u−v)`, whose
     energy is `2(u²+v²)`). The coordinate pair splits
     orthogonally and has zero defect
     (`defect_evenFst_evenSnd`); the other two pairs share the
     strict midpoint defect
     `2·log θ(2s) − log θ(s) − log θ(4s) < 0`
     (`defect_evenFst_evenSum_eq_evenSnd`,
     `defect_evenFst_evenSum_neg`, `defect_evenSnd_evenSum_neg`).
     The exact order-3 recurrence kills all three pairwise terms
     and leaves the field gap across the distributivity-defect
     interval `[2ℤ², {a+b even}]` (`distrib_interval`), so
     `D₃ = 2·log(θ(2s)/θ(4s)) > 0` (`defect3_diamond`,
     `defect3_diamond_eq`, `defect3_diamond_pos`, using the strict
     decrease of `theta` on positive couplings, `theta_lt_theta`),
     and `D₃ → log 2` as `s → 0⁺` (`tendsto_defect3_diamond`).
     The contrast is packaged: every pairwise observation on the
     realized diamond is nonpositive
     (`defect_diamondHom_nonpos`) while this order-three one is
     positive. And the limit is an index: each atom has index two
     in `ℤ²` (`index_evenFst`, `index_evenSnd`, `index_evenSum`),
     the doubled lattice has index two inside the checkerboard
     (`relIndex_evenBoth_evenSum`), and the boundary value is the
     logarithm of that relative index
     (`tendsto_defect3_diamond_index`).

   This closes the original resolution-tower question and opens the
   genuinely new one on non-distributive sublattice carriers.

   **Consider upstreaming to Descent:** if the coprime telescope
   naturally produces a reusable theorem for pairwise-disjoint
   families on distributive lattices, Descent may eventually want
   that abstraction. Theaetetus will prove and use the needed
   specialization locally; this note creates no upstream task and
   does not block the target.
8. **The star obstruction** — done (`deficit_not_psd`,
   `cnd_not_psd` in `Theaetetus.StarObstruction`): the explicit
   star-weight witness closed it without eigenvalue machinery.
   What remains under this heading is the rate (Q4-PSD).
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
10. **The equality chain.** Zero defect forces simultaneous
    saturation of every inequality in the correlation proof:
    collinearity of the parity feature vectors in Cauchy–Schwarz,
    the AM–GM equality `m(x+y) = m(x−y)`, and the saturation of
    each residue-class instance in the dilation and coprime
    telescopes. The two analytic links are done
    (`Theaetetus.CorrelationEquality`), and as biconditionals:
    Cauchy–Schwarz equality is exactly positive collinearity of the
    two parity feature vectors (`ParityCollinear`,
    `gramMass_sq_mul_sq_eq_iff`), resting on a general criterion
    for strictly positive finite vectors
    (`sum_mul_sq_eq_sq_mul_sq_iff_of_pos`, by the Lagrange
    identity), and the averaged bound is an equality exactly when
    that collinearity holds together with the reflected-mass
    equality `m(x+y) = m(x−y)` (`gramMass_mul_eq_avg_iff`) — which
    collapses further to literal equality of the two parity feature
    vectors (`gramMass_mul_eq_avg_iff_parityVector_eq`), the
    canonical form for the chain, the conjunction being kept to
    expose the two links separately. The dilation-level residue
    saturation is done too: both sides of `gramMass_dilate_mul_le`
    are sums over residue classes of the same averaged bound at the
    named shifts `dilateShift n x` and `residueShift n c`
    (`gramMass_dilate_mul_eq_sum`, `gramMass_dilate_avg_eq_sum`),
    a dominated sum meets its dominating sum exactly when every
    term does (`sum_eq_iff_of_le`), and so scalar dilation is an
    equality exactly when every residue class is
    reflection-invariant (`gramMass_dilate_mul_eq_iff`). The
    coprime resummation closes the same way one grid out: both
    sides of `gramMass_coprime_mul_le` are sums over the `b`-grid
    of the two sides of dilation monotonicity at the outer shifts
    `dilatedResidueShift a b r` (`gramMass_coprime_mul_eq_sum`,
    `gramMass_coprime_avg_eq_sum`, the second through the named
    unit resummation `sum_gramMass_dilatedResidueShift`), so
    equality is class-by-class saturation
    (`gramMass_coprime_mul_eq_iff_forall_class`), and since the
    outer shift normalizes
    (`dilateShift_dilatedResidueShift`) the criterion is two-grid
    (`gramMass_coprime_mul_eq_iff`): correlation at coprime
    dilations is an equality exactly when

        P(v_r + v_c) = P(v_r − v_c)   for all r mod b, c mod a,

    with `P` the parity feature vector at the joint scale — every
    point of the `b`-grid a reflection center for the `a`-grid.
    Each equality has reflection form. Whether the sampled fibers
    close under composition strongly enough to force a nontrivial
    translation is part of the remaining rigidity problem. The
    chain now reaches
    the defect itself. For a positive field, vanishing at a coprime
    pair is exactly multiplicativity across the rectangle
    `{a, b, 1, a·b}` (`fieldDefect_eq_zero_iff_mul_eq`, generic and
    logarithm-only), so a vanishing Gram defect is exactly the mass
    identity (`gramDefect_eq_zero_iff_mul_eq`) and hence exactly
    the criterion (`TwoGridReflection`,
    `gramDefect_eq_zero_iff_twoGridReflection`); intrinsically, a
    lattice action has zero defect at a coprime pair exactly when
    the criterion holds in an integral chart
    (`QuadLatticeAction.defect_eq_zero_iff_twoGridReflection`), and
    therefore in one chart exactly when in every other
    (`QuadLatticeAction.twoGridReflection_gram_iff`). The equality
    chain is complete through the intrinsic two-grid criterion.

    The sole mathematical remainder is one rigidity statement: in
    positive rank, for coprime `a, b > 1`, the two-grid parity
    reflection condition is impossible. Once that theorem exists,
    `fieldDefect_div_gcd` reduces an arbitrary pair to its coprime
    base and turns the equivalence into the full equality
    classification. The target is specifically scalar dilations:
    the index-two diamond shows that arbitrary incomparable
    sublattices may saturate by orthogonal splitting
    (`defect_evenFst_evenSnd`), so the rigidity must use
    coprimality of the scalar pair, not merely incomparability.
    This is the route to Q1's equality classification that is
    independent of higher-rank Q5.
11. **The resolution metric.** Import Descent's join-kernel
    pseudometric theorem through the same package boundary as target
    7 and instantiate it with the normalized field
    `q ↦ -log Z(q²s)`. The landing is

        d_s(q,q′) := log (Z(q²s)·Z(q′²s) / Z(lcm(q,q′)²s)²),

    a pseudometric on positive resolutions for every lattice and
    scale; prove separation for every nontrivial partition tower,
    making it a metric. At rank one and coprime `p,q`, record
    `⟨p,q⟩ = d_s(1,pq) − d_s(p,q)`. This supplies the intrinsic
    metric geometry in which Q4's CND/Schoenberg question naturally
    lives. Completion and diameter claims remain outside the target
    until they are proved.
12. **The distributivity-index law.** Conjectural, and stated as
    such. For full-rank finite-index sublattices `A, B, C`, with
    `U = (A+B) ∩ C` and `V = (A∩C) + (B∩C)` the two ends of the
    distributivity-defect interval, the landing is

        D₃,s(A,B,C) → log [U : V]   as   s → 0⁺,

    the order-three defect at the boundary reading off the index
    of the interval the recurrence leaves behind. The proved `M₃`
    diamond of target 7 is its first nontrivial case: there
    `[U : V] = 2` (`relIndex_evenBoth_evenSum`) and the limit is
    `log 2` (`tendsto_defect3_diamond_index`). The route follows
    that proof: at the boundary every pairwise term vanishes by
    multiplicativity of covolume in the Gaussian mass, and
    `defect3_recurrence` leaves the mass gap from `V` to `U`,
    whose ratio tends to the index. First prove the Gaussian
    mass-ratio limit for a finite-index inclusion `V ≤ U`; then
    combine it with pairwise covolume cancellation and
    `defect3_recurrence`. Until then this is a conjecture with one
    witness, not a theorem with a general proof.

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
   Next: apply the certification chain (target 5) to the
   deep-degeneration margins.
2. **Q4 phase geometry** — first uncertified sweep complete
   (`recon/q4.py`; `q4_sweep_*.json`, `q4_witness.json`;
   findings in `recon/README.md`): correctly-oriented extremal
   eigenvalues, one detected sign change per statistic per
   sampled grid with brackets bisected, and the historically
   cited transitions and `s = 0.12` witness reproduced from
   committed code. Next: apply the crossing algebra (target 5) to
   certify the entry intervals and brackets, further intervality
   falsification, and the star-obstruction rate against its
   `s_PSD ~ (1/6)·log n` benchmark.

The sequence so far: the restructuring, strict Q5 for diagonal
forms, the dual-aware harness, the rank-two and rank-three
sweeps, the first Q4 sweep, the star-obstruction theorem, the
manifest with its docstring sweep, the recovery formula, spectral
peeling, the certification chain, higher-rank defect duality, and
the Regev–Stephens-Davidowitz implication are complete, and the
orthogonal-sum reduction has closed the remainder of target 2.
The higher-interaction bridge (target 7) is complete: the seam,
the coprime telescope with its sign laws, the raw-difference
isolation, and the Gaussian `M₃` diamond, whose order-three defect
is strictly positive and survives the small-scale boundary. Still
open: the equality chain (target 10), complete through the
intrinsic two-grid criterion and awaiting only the rigidity
theorem that the criterion is impossible for coprime `a, b > 1`;
the resolution metric (target 11); and the distributivity-index law
(target 12), a conjecture whose first nontrivial case is that
diamond. The
verdicts to date: Q5 stays a universal conjecture, with margins
vanishing toward every degenerate boundary probed and its binding
point leaving the duality center under dual asymmetry; Q4's
uniform-PSD question is resolved negatively by the star
obstruction, leaving the rate and intervality open.

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
