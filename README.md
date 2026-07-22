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

## The theorems

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
  (`tendsto_defect_succ`, `eventually_defect_neg`). Instances:
  rank-one theta (`defect_eq_thetaTower_defect`), every graph
  carrier — where the cross-ratio law identifies the
  residue-complexity defect with the tower's
  (`towerDefect_eq_partitionTower_defect`,
  `towerDefect_forall_eq_zero_iff`) — and **every positive-definite
  lattice action** (`QuadLatticeAction.toPartitionTower`).
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
the log-primes. Both all-scale sign proofs already used the
reflection inline (`Sign`, branch two; `Submodular`, reflection
branch), each re-deriving the cancellation for its own pair; the
law is now stated once — the rectangle engine and the arithmetic
law (`theta_rect_dual`, `defect_dual`), the coprime evenness
(`defect_scale_even`), and the inequality equivalence the
reflection branches consume (`theta_rect_lt_iff`).

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
reflected scales. The higher-rank statement remains unformalized.

## The questions

- **Q1 — strictness and generic residue actions.** Regev and
  Stephens-Davidowitz prove that two sublattices `M,N ⊆ L` are
  positively correlated under normalized Gaussian mass:
  `ρ(M)·ρ(N) ≤ ρ(L)·ρ(M ∩ N)`
  ([*An Inequality for Gaussians on Lattices*](https://doi.org/10.1137/15M1052226),
  Theorem 5.1). Apply this inside `gL`, with `g = gcd(q,q′)`, to
  `qL` and `q′L`; their intersection is `lcm(q,q′)L`, and
  quadratic scaling gives exactly `D_L(q,q′) ≤ 0`. This implication
  is not yet formalized. A generic residue tower on `L ⧸ qL` would
  make the correlation an intrinsic event statement and supply the
  general-lattice cross-ratio law. The remaining sign question is the
  equality case: on a positive-rank lattice, is `D_L(q,q′) = 0` iff
  `q ∣ q′` or `q′ ∣ q`?

- **Q2 — sparse spectral rigidity.** Put
  `F(m) := log Z(m²)` for `m ≥ 1`. Saturation gives an inverse
  formula using only coprime defect entries:

      F(m) = lim_{k→∞} D(m, km+1) − lim_{n→∞} D(n+1, n+2).

  This remains to be formalized at `PartitionTower` level. Joint
  saturation of the prime pairing recovers `F(1)`, while for fixed
  prime `p`, the limit along primes `q → ∞`, `q ≠ p`, recovers `F(p)`
  through `lim ⟨p,q⟩ = F(1) − F(p)`. Do these prime samples determine
  the locally finite energy spectrum by successively extracting its
  least energy and multiplicity? Equivalently, does the full
  prime-pairing matrix determine the theta series, making equality of
  scalar defect matrices equivalent to theta-equivalence? Does one
  infinite prime row already suffice, and what is the minimal
  determining subset of defect entries? The reflection law acts on
  the all-scale defect field, not on a fixed-`s` matrix: reflected
  scales vary with the pair, so a single matrix is untouched by
  duality while the field determines its own reflection. Rigidity
  statements should say which datum they consume.

- **Q3 — the residue-refined inverse problem.** Scalar defect data
  cannot distinguish theta-equivalent lattices; sparse spectral
  rigidity would make theta-equivalence exactly its kernel. Which
  refinement of the modal scalar — the complete coset-mass vector on
  `L ⧸ qL`, its finite Fourier transform, or a smaller collection of
  characters — determines the quadratic lattice up to isometry? For
  graph carriers, does the corresponding invariant determine graph
  isomorphism, cycle-matroid equivalence, or a coarser relation?

- **Q4 — scale-dependent kernel geometry.** For which scales is
  the prime pairing conditionally negative definite (CND), and for
  which scales is its saturation deficit positive semidefinite?
  The two clauses share one structure. Write `F(m) := log θ(m²s)`,
  `h_s(x) := log θ(s·e^{2x})`, `x_p := log p`. On distinct primes
  the pairing is the Hankel-cocycle second difference
  `⟨p,q⟩ = h_s(0) + h_s(x_p+x_q) − h_s(x_p) − h_s(x_q)` with true
  diagonal zero; writing `M̃` for that formula extended to all
  pairs — the Hankel-cocycle extension —
  `M = M̃ − diag(d_s(x_p))`,
  where `d_s(x) = h_s(0) − 2h_s(x) + h_s(2x)` is a Q5 curvature —
  the coupling between this question and Q5. The saturation
  deficit `B := log θ(s)·J − M` has exact entries
  `B_pq = F(p) + F(q) − F(pq)` off the diagonal and `F(1)` on it;
  it is entrywise positive (`pairing_lt_base`), and
  `cᵀBc = −cᵀMc` on zero-sum vectors, so deficit-PSD implies CND
  outright — and only that: the converse fails numerically.

  The chambers, numerically. Define
  `s_c(P) := inf { s₀ : the kernel on P is CND for all s ≥ s₀ }`,
  and likewise for the deficit. On `{2,3,5}` the transitions sit
  near `0.080` (CND) and `0.085` (deficit-PSD); on `{2,3,5,7,11}`
  near `0.108` and `0.169` — at `s = 0.12` the five-prime pairing
  is CND while its deficit is not PSD. The clauses are coupled but
  distinct, and enlarging the prime set only shrinks the
  valid-scale sets. Both asymptotic regimes have identified
  mechanisms, stated as targets. Large `s`: on zero-sum vectors
  the row and column terms of `M` cancel identically and the lcm
  term is controlled through `(pq)² ≥ p² + q²`, suggesting a route
  to an absolute threshold — the existing bounds are entrywise,
  and the missing step is the dimension-free quadratic-form
  estimate; the binding inequality `log θ(s) ≥ 2·log θ(4s)`
  crosses near `s = 0.196`, and the first hundred primes are CND
  at `s = (log 2)/3`. Small `s`: the reflection law evaluates each
  entry at its own dual scale, `⟨p,q⟩ = 2e^{−σ}(1 + O(e^{−σ}))`
  with `σ = π²/(s·p²q²)`; entries are hierarchically separated,
  the largest product dominates, and the zero-sum weight putting
  `(1, 1)` on the two largest primes and `−2` on a third is
  positive — no set of three or more primes stays CND as `s → 0`.
  Open: whether each valid-scale set is an interval; whether
  `sup_P s_c(P)` is finite; how the deficit transition scales with
  the prime set.

  The transform question has a sharpened target. Saturated rows
  obstruct any Gram representation of `B/2` by Dirichlet monomials
  `p^{−λ}` against a shared measure: the row limit `B_pq → F(p)`
  as `q → ∞` depends on `p`, while `∫ p^{−λ}q^{−λ} dν → ν({0})`
  does not. Survival vectors `𝟙[t ≥ p]` in `L²(−dF)` split off a
  canonical PSD component with Gram kernel `F(max(p,q))`, but the
  remainder `F(min(p,q)) − F(pq)` (diagonal `F(1) − F(p)`) keeps
  the same `p`-dependent row limit `F(p)`: the obstruction
  survives the subtraction, and realizing the remainder is the
  open problem.

- **Q5 — thermodynamic curvature.** A continuous strengthening of
  the sign asks whether

      u ↦ log Z_L(exp u)

  is convex for every positive-definite lattice. Its second
  derivative is the fluctuation inequality
  `β² Var_β(E) − β ⟨E⟩_β ≥ 0`. Convexity would imply every
  discrete defect inequality at once, for arbitrary real resolution
  ratios, and would explain the sign as thermodynamic curvature rather
  than a collection of arithmetic comparisons. The Gibbs
  expectation/variance interface and multivariate Poisson summation
  provide the analytic ingredients for this question.

  The question is exactly the sign of the Poisson correction: the
  continuum Gaussian has `⟨E⟩ = n/(2β)` and `Var = n/(2β²)`, so
  its curvature vanishes identically. Three consequences of the
  symmetry sharpen the target. The coarse half is latent in the
  formalized sign: the `b → a` limit of `theta_prod_lt_general`
  gives `θ(a²t)² ≤ θ(t)·θ(a⁴t)` for every real `a ≥ 2` — midpoint
  convexity of `H` at every location at leg spacing `≥ 2 log 2`,
  which in particular makes every Q4 diagonal correction
  `d_s(x_p)` nonnegative, since `x_p ≥ log 2`. The hypothesis
  `2 ≤ a` originates in integer incomparability and may be
  analytically unnecessary; Q5 at rank one is the conjecture that
  the inequality never needed the integers. It is equivalent to
  the non-strict equal-leg case `θ(a²t)² ≤ θ(t)·θ(a⁴t)` for
  `1 < a < 2`; the strict two-leg extension of
  `theta_prod_lt_general` to `1 < a` is a stronger sufficient
  target. The reflection makes
  the curvature invariant under `β ↦ π²/β` at rank one and pairs
  it with the dual lattice at higher rank,
  `H_L″(u) = H_{L*}″(2·log π − u)`: convexity for every lattice on
  `β ≥ π` is convexity everywhere, the class being closed under
  duality — an individual profile is self-symmetric only when the
  lattice is isodual. And differentiating the duality at its fixed
  point gives the anchor `θ′(π) = −θ(π)/(4π)` — mean Gibbs energy
  exactly `1/(4π)` at the self-dual scale — cheap through
  Mathlib's `differentiableAt_jacobiTheta`; only the Gibbs reading
  needs the termwise bridge.

- **Q6 — higher association and realizability.** The correct
  algebraic object is the symmetric mixed-difference hierarchy of
  `K` on the prime-exponent lattice: `Δ_{p₁}⋯Δ_{p_k}K` measures
  `k`-prime coupling. The pairing matrix is this hierarchy's
  `k = 2` layer, and Q4's saturation deficit is its union form
  `F(p) + F(q) − F(pq)` off the diagonal: Q4's kernel geometry is
  the definiteness theory of the first nontrivial level. Rectangle identities and
  the characterization
  of vanishing cross-prime differences are formalization work, not
  open mathematics. Numerical evidence in rank one indicates that the
  three-prime difference at `2,3,5` changes sign with the scale, so
  the relevant structure is a system of sign chambers rather than a
  uniform alternating-sign law. Which asymptotic regimes and
  inequalities survive beyond pairwise correlation, and which mixed
  Hessians are realizable by lattice theta functions? Because `K` is
  an intersection surprisal rather than an entropy, entropic-cone
  membership is a separate representation problem.

## The ladder

The formalization order for the symmetry and its consequences.
Rungs 1–3 are complete (`Theaetetus.Duality`, with the corollary
`theta_rect_lt_iff`). Rungs 4–5 are independent of the engine,
rung 6 consumes rung 2, rung 7 subsumes rung 4:

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
5. The large-scale chamber — target: an absolute `s₀` beyond
   which the prime pairing is CND on every finite prime set. The
   zero-sum cancellation and `(pq)² ≥ p² + q²` mark the route;
   the dimension-free quadratic estimate is the work.
6. The small-scale chamber — every set of three or more primes
   fails CND for all sufficiently small `s`.
7. `theta_prod_lt_general` with `1 < a` — the open core; with
   continuity it closes Q5 at rank one.

## The map

The root module [`Theaetetus.lean`](Theaetetus.lean) imports every
module under a one-line section comment, in logical order from the
analytic primitive to the rank-two witness. That import list is the
table of contents: it compiles, so it cannot drift. Each module's
docstring carries its local story.

## Building

    nix develop -c lake build        # or: nu tasks.nu check

Toolchain `leanprover/lean4:v4.26.0`, Mathlib pinned at `v4.26.0`.
Zero `sorry`, zero `axiom` declarations; `lake build` green is the
only definition of done. Where a desired statement fails, the
counterexample becomes a theorem. Version control is jujutsu.

## History

Built in eight milestones, `M0`–`M7` (labels that still appear in
docstrings): scaffold; the scalar core and chain-vanishing; the
witness `θ(4/3)·θ(3) < θ(1/3)·θ(12)`; the sign at `(2,3)` for all
scales; the carrier — graph homology, the residue tower, the
cross-ratio law, the rank-two witness; outward — Q1 closed at rank
one, the pairing, the rank function, the kernel on `C₃`; the
reconciliation — the defect as conditional association, the sign
for diagonal forms in every rank, Q3 classified for every carrier;
the interface — the partition tower, the classification proved once
abstractly, with rank one, every graph carrier, and every
positive-definite lattice action as instances.
