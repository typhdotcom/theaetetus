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

```
D(q, q′) := [log Z(q²) + log Z(q′²)] − [log Z(gcd²) + log Z(lcm²)].
```

On a graph carrier the analytic formula carries its intended reading
as a theorem: a resolution `q` induces a **residue action** on
`H¹(G;ℤ) ⧸ qH¹(G;ℤ)` with complexity `K(q)`, and the cross-ratio
law proves `D(q,q′) = [K(lcm) + K(gcd)] − [K(q) + K(q′)]`
(`crossRatio_law`). Deriving that reading from residue actions on
`L ⧸ qL` for an arbitrary lattice is part of Q3; until then the
general defect **is** the cross-ratio.

`D ≡ 0` would say `q ↦ log Z(q²)` is a valuation on the
divisibility lattice — `Z(gcd²)·Z(lcm²) = Z(q²)·Z(q′²)`, the
resolution tower localizing over the primes. That is not an Euler
product of the form's Epstein zeta: the hexagonal form below has
one (its Epstein zeta is a multiple of `ζ(s)·L(s, χ₋₃)`), yet its
defect at `(2,3)` is strictly negative
(`thetaGraph_towerDefect_neg`). For the towers formalized here it never is, unless
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

- **Coset duality.** Poisson summation sends the shifted mass
  `gramMass M α y` to the character-twisted dual Boltzmann sum
  `twistTheta M⁻¹ y (π²/α) = ∑_m cos(2π⟨m, y⟩)·e^{−(π²/α)·mᵀM⁻¹m}`
  with the weight of `gramTheta_dual` (`gramMass_dual`), so the
  twisted sum is positive (`twistTheta_pos`) and the shifted defect
  reflects onto the twisted one, shift for shift
  (`shiftDefect_dual`). The mass of a residue class `c + 2ℤᵈ` is the
  shifted mass at quadrupled coupling and half shift
  (`cosetMass_eq_gramMass`), with character `(−1)^⟨m,c⟩`
  (`cos_dualPairing_halfShift`), so the classwise defect reflects
  class by class onto the twisted dual field at scale
  `π²/(4·lcm²·s)` (`cosetDefect_dual`).

- **The classwise defect has no sign.** The scalar defect is
  nonpositive (`gramDefect_nonpos`); a class without a zero vector
  is not. At rank one the odd class has mass squeezed between
  `2e^{−β}` and `4e^{−β}` for `β ≥ 1` (`two_exp_le_oddMass`,
  `oddMass_le_four_exp`), and its defect at `s = 1`, `(2, 3)` is
  strictly positive (`cosetDefect_odd_pos`). The sign belongs to
  the zero-energy sector.

  Adelically, these are local θ-functions: `cosetMass` is the
  `S = {∞, 2}` θ-function `Σ_{ξ} f(ξg)` of a Gaussian times a
  residue indicator, `twistTheta` its character twist, and
  `cosetDefect_dual` the Tate functional equation `f ↦ f̂`. The
  dilation tower moves the idele at the primes dividing the
  resolution. Traces and Mellin transforms are linear in `f` and
  factor place by place; the defect is the logarithmic coupling
  between places that such linear functionals do not see.

- **Coset separation, rank four.** For an integral Gram matrix,
  the class pairs at energy `m` — ordered pairs of distinct sectors
  of energy `m` congruent modulo `2` — are carried bijectively by
  every integral isometry (`classPairs_ncard_eq_of_isometry`).
  Schiemann's quaternary pair (determinant `1729`), which has a
  single theta series, has ten sectors each at energy `12`
  (`schiemannA_shell`, `schiemannB_shell`) but `10` and `18` class
  pairs there (`schiemannA_classPairs_ncard`,
  `schiemannB_classPairs_ncard`), so the mod-`2` residue datum
  separates what every scalar defect identifies
  (`schiemann_not_isometric`). The shells are certified by
  diagonal dominance as a sum of squares and a kernel check of the
  box `[-3, 3]⁴`. Equality of the two theta series is not
  formalized.

- **Frame separation, rank sixteen.** In an even positive form two
  energy-four sectors congruent mod `2` are equal, opposite or
  orthogonal (`pairing_of_congr_four`), so a mod-`2` class holds at
  most `2n` of them (`frame_card_le`). On `E8 ⊕ E8` (Cartan blocks,
  positive by an `LDLᵀ` certificate) every class holds at most 16
  (`e8sq_class_card_le`), while `D16⁺` has the class of the 32
  sectors `±2eᵢ` (`d16plus_frame`): the mod-`2` residue datum
  separates the theta-equivalent pair
  (`e8sq_not_isometric_d16plus`). Equality of their theta series
  (`E₄²`) is not formalized.

- **Class pairs are degree-two Siegel data.** For a symmetric
  positive-definite integral Gram matrix, class pairs at energy `m`
  are the disjoint union over `t ≠ 0` of the representation sets of
  the binary Gram matrices `!![m, −t; −t, t]`
  (`classPairsEquivSigma`), so equal degree-two representation
  numbers force equal class-pair counts
  (`classPairs_ncard_eq_of_siegelSet`). Schiemann's pair therefore
  has distinct degree-two representation numbers
  (`schiemann_siegelSet_ne`): the theta series it shares in
  degree one (a numerical fact here) splits in degree two.
  In every degree, injective `k`-tuples of energy-`m` sectors in
  one class are a Gram predicate on the first sector and the half
  differences (`classTuplesEquivPred`), so equal representation
  numbers in degree `k` give equivalent class tuples
  (`classTuplesEquivOfSiegel`). With the frame bounds this
  separates `E8 ⊕ E8` from `D16⁺` in degree 17
  (`e8sq_d16plus_siegel_ne`); their known separation is in degree
  4, where the recon's fourth class moments split.
  The coefficient of the classwise degree-four law is Siegel data
  too: quadruples of energy-`m` sectors summing into `2ℤⁿ` are a
  Gram predicate on `(u₀, u₁, u₂, w)`, `u₃ = 2w − u₀ − u₁ − u₂`, so
  equal degree-four representation numbers give equivalent even
  quadruples (`evenQuadsEquivOfSiegel`).

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

```
D_s(q, q′) = D_{π²/(s·lcm²)}(q/g, q′/g),    g := gcd(q, q′).
```

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

In Arakelov terms, `log Z_L(π)` is the arithmetic `h⁰` of the
lattice with its Gaussian metric, and Poisson summation is
arithmetic Riemann–Roch: `h⁰(L) − h⁰(L*) = −log covol(L)` up to
normalization. The prefactors the cross-ratio annihilates are the
Euler characteristic `χ = −log covol`, which is a valuation on the
dilation tower (`covol(qL) = qʳ·covol(L)`). So the defect of `h⁰`
on `L` is the defect of `h¹ = h⁰(L*)` at the reflected scale,
`χ` carries none of it, and at the boundary `s → 0`, where `h¹`
vanishes and `h⁰ → χ`, so does the defect. On the Dirichlet side
the same cancellation is total: dilation multiplies the Epstein
zeta by `q^{−2s}`, a character of `q`, so every defect is
invisible to Euler-product and covolume data and lives in the
logarithm of the theta sum itself.

## The questions

Three strata are kept apart: closed results live in **What is
established** (formal theorems alongside numerical counterexamples
and explicit nonclaims), known-but-unformalized implications and
their numbered targets in [`ROADMAP.md`](ROADMAP.md), and this
section keeps only statements whose truth is unknown. Every inverse
question names the datum it consumes. The organizing axes: rank
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

  ```
  F_s(m) = lim_{k→∞} ( D_s(m, km+1) − D_s(k+1, k+2) )
  ```

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
  settles. First numerical record (`recon/q3.py`): the
  theta-equivalent even unimodular pair `E8 ⊕ E8`, `D16⁺` is
  separated by its mod-2 coset theta series already at norm 4 —
  one class of `D16⁺ ⧸ 2D16⁺` holds 32 norm-4 vectors, while no
  class of `E8² ⧸ 2E8²` holds more than 16 — and not by the mod-3
  series through norm 6. The separation has a precise order. The
  `k`-th falling moment of the per-class counts counts `k`-tuples
  in one class, a Gram-matrix condition on `k` lattice vectors,
  so it is fixed by the degree-`k` Siegel theta series; the
  moments agree for `k ≤ 3` and first differ at `k = 4`, the
  degree at which the Siegel theta series of the pair are known
  to separate. Coset data reaches below theta-equivalence
  through higher-degree correlations, and a refinement of the
  datum is measured by the Siegel degree it reaches. Schiemann's
  quaternary theta-equivalent pair separates one degree earlier:
  its second falling moment differs at every modulus tried
  (`q = 2, 3, 5, 7, 13, 19`, once the energy bound reaches the
  informative range), and at `q = 2` the separation is a theorem
  (`schiemann_not_isometric`). The same
  order governs the classwise defect, the cross-ratio of
  `log Θ_{c+2L}` along the dilation tower (`recon/q3field.py`):
  Poisson summation reflects it class by class onto the
  character-twisted field (`cosetDefect_dual`), and summed over classes it separates
  the pair by `(2¹⁶/4)·ΔN₄·e^{−8t}` at small scale, `N₄` the root
  quadruples summing into `2L` — fourth order, with the predicted
  coefficient matched to `3·10⁻⁵` at `t = 8`. The sign does not refine:
  every class without a zero vector has eventually positive
  defect, `D_c → s·m_c·(q² − 1)(q′² − 1)` with `m_c` its minimal
  norm, so the nonpositive sign belongs to the zero-energy sector.

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
  The pairing matrix on a finite positive sample is Descent's sampled
  defect matrix of the normalized field `−log θ(q²s)`
  (`pairingMatrix_eq_defectMatrix`), and `IsCNDOn` is its
  `CondNegSemidef` (`isCNDOn_pairing_iff`), so both chambers read
  in Descent's vocabulary (`condNegSemidef_resField_large`,
  `not_condNegSemidef_resField_small`). The prime-only sample is
  forced: against a least element the defect vanishes, the centred
  Gram kernel at it is minus half the matrix, and the matrix is
  then CND only if it is zero
  (`Descent.condNegSemidef_defectMatrix_iff_of_base`) — a positive sample
  containing `1` is CND exactly when it is a divisibility chain
  (`isCNDOn_pairing_iff_chain_of_one_mem`), so `1` with two
  distinct primes never is (`not_isCNDOn_pairing_one_prime_prime`).
  Open is the geometry
  of the middle, one clause per matrix. **Q4-CND**: for a finite
  prime set `P`, is the valid-scale set
  `{ s : pairing CND on P }` an upper interval? The controlling statistic is the largest eigenvalue of the
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
  consistent with intervality, still unproven. The
  transform-realization question seeds Q7. A second geometry is
  visible as well: the join kernel of `q ↦ -log Z(q²s)` is the
  resolution distance in target 11, and on coprime primes the
  pairing is a difference of two of its distances.

- **Q5 — higher-rank thermodynamic curvature: the master
  conjecture.** Rank one is closed (established, the refined
  log-convexity); the whole goal is now: for every
  positive-definite lattice `L` of positive rank — rank zero has
  constant `H`, convex but never strictly — is

  ```
  u ↦ H_L(u) := log Z_L(exp u)
  ```

  strictly convex — equivalently, does the coupling-weighted
  fluctuation beat the mean, `β²·Var_β(E) > β·⟨E⟩_β`? The
  continuum Gaussian has `⟨E⟩ = n/(2β)`, `Var = n/(2β²)`, so its
  curvature vanishes identically: the conjecture lives entirely
  in the Poisson corrections. The stakes are exact. Resolutions
  scale the form uniformly, so with `u = log s + 2·log g`,
  `x = 2·log(q/g)`, `y = 2·log(q′/g)`,

  ```
  D_L(q,q′) = [H_L(u+x) + H_L(u+y)] − [H_L(u) + H_L(u+x+y)],
  ```

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
  Fact-1 mechanism, universal. The duality transports it to
  small coupling for `L*`, and this step is a theorem: the Gram
  Boltzmann sum differentiates termwise, with mean energy and
  variance its first and second logarithmic derivatives
  (`hasDerivAt_log_gramTheta`, `hasDerivAt_gramMeanEnergy`); the
  Gram reflection differentiates to
  `β·⟨E⟩_M(β) + (π²/β)·⟨E⟩_{M⁻¹}(π²/β) = d/2`
  (`gramMeanEnergy_dual`) and then to equality of the curvature
  `β²·Var − β·⟨E⟩` of `M` at `β` and of `M⁻¹` at `π²/β`
  (`gramCurvature_dual`), which is `H_L″(u) = H_{L*}″(2·log π − u)`
  since the curvature is `H_L″` at `u = log β`
  (`logCurvature_gramTheta`). So strict convexity for `L` and `L*`
  on `β ≥ π` is strict convexity for `L` everywhere
  (`gramCurvature_pos_of_ge_pi`; intrinsically
  `QuadLatticeAction.logCurvature_dual`,
  `QuadLatticeAction.logCurvature_pos_of_ge_pi`) — the class closed
  under duality, an
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

  ```
  D_k(q₁,…,q_k) = Σ_{j=1}^{k−1} D(q_j, q_{j+1}⋯q_k),
  ```

  proved for the log-partition field of any `Z` at any scale
  (`defectFam_logField_eq_telescope`). The telescope is Descent's:
  coprimality is disjointness on the divisibility carrier, and a
  pairwise disjoint family in a distributive lattice loses both
  correction terms of the exact recurrence
  (`Descent.Arith.defectFam_eq_telescope_of_pairwise_coprime`);
  Theaetetus reads it arithmetically, the join of a coprime family
  being its product (`supFam_of_pairwiseCoprime`,
  `telescope_eq_descent_telescope`). Eliminating from the front prices
  each entry against the product of those following it, but the
  total does not depend on that order: the telescope computes the
  symmetric abstract defect, so any two presentations of the same
  coprime family agree (`telescope_eq_of_perm`). At arity three
  this is the coherence identity

  ```
  D(a,b) + D(ab,c) = D(b,c) + D(a,bc),
  ```

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

  ```
  raw(a,b,c) = D(a,c) + D(b,c) − D(a·b,c)
  ```

  (`mixedDiff_triple_of_pairwiseCoprime`): the raw cube is its
  three pairwise faces minus the corrected defect, the corrected
  defect is itself pairwise on this distributive carrier, the
  meet-derived term `D(a ⊓ c, b ⊓ c)` collapses to `D(1,1) = 0`,
  and the shared face `D(a,b)` cancels. At `2,3,5` this reads

  ```
  raw(2,3,5) = D(2,5) + D(3,5) − D(6,5)
  ```

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

  ```
  D₃ = log ρ({a+b even}) − log ρ(2ℤ²) = 2·log(θ(2s)/θ(4s)) > 0
  ```

  (`defect3_diamond`, `defect3_diamond_eq`, `defect3_diamond_pos`
  in `Theaetetus.SublatticeDiamond`), tending to `log 2`, the
  logarithm of the index of the doubled lattice inside the
  checkerboard, as the scale falls to zero
  (`tendsto_defect3_diamond`).
  So off distributivity `D₃` does not descend to pairwise data,
  while the hierarchy stays observationally capped at order three.
  Every pairwise observation on that five-point carrier is
  nonpositive (`defect_diamondHom_nonpos`); the positive
  order-three one is the formal contrast. It also places the
  Gaussian diamond outside Descent's finite Gibbs class, whose
  realizations of the diamond are constant and attain only the zero
  canonical datum: the Gaussian datum is
  `(0, m, m, 2·log(θ(2s)/θ(4s)))`, `m` the midpoint defect
  (`canonicalDatum_diamondHom`), excluded with its negation
  (`not_canonicalDatumRealizable_diamondHom`); the field itself
  fails the realizable sign (`not_realizable_diamondHom`), and its
  negation, which passes it, is excluded by constancy alone
  (`not_realizable_neg_diamondHom`).

  The boundary value being an index is general. For finite-index
  subgroups `A, B, C` of `ℤᵈ`, each priced by the logarithm of its
  euclidean Gaussian mass (`subField`), put `U = (A+B) ∩ C` and
  `V = (A∩C) + (B∩C)` — the two ends of the distributivity-defect
  interval (`distribUpper`, `distribLower`). Then

  ```
  D₃,s(A,B,C) → log [U : V]   as   s → 0⁺
  ```

  (`tendsto_defect3_subField`): at the boundary every pairwise
  term tends to zero by multiplicativity of covolume
  (`tendsto_defect_subField`), and `defect3_recurrence` leaves
  exactly the Gaussian mass gap from `V` to `U`, whose ratio tends
  to the index. The diamond is the first nontrivial case,
  `[U : V] = 2` (`relIndex_evenBoth_evenSum`,
  `tendsto_defect3_diamond_index`). Open beyond it: other ambient
  positive-definite forms on `ℤᵈ`, rank loss and infinite index
  (where covolume no longer normalizes the masses), the equality
  mechanisms — when `D₃` vanishes, or reaches its boundary value,
  at positive scale — and the interaction of this order-three
  observable with lattice duality.

- **Q7 — realizability.** Which abstract hierarchies actually come from
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

```
nix develop -c lake build        # nu tasks.nu check adds nix flake check
```

Without nix, with `elan` installed: `lake exe cache get`, then
`lake build`.

Toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned at `v4.34.1`.
Zero `sorry`, zero `axiom` declarations; `lake build` green is the
only definition of done. Where a desired statement fails, the
counterexample becomes a theorem. Version control is jujutsu.
