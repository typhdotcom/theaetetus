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
  determining subset of defect entries?

- **Q3 — the residue-refined inverse problem.** Scalar defect data
  cannot distinguish theta-equivalent lattices; sparse spectral
  rigidity would make theta-equivalence exactly its kernel. Which
  refinement of the modal scalar — the complete coset-mass vector on
  `L ⧸ qL`, its finite Fourier transform, or a smaller collection of
  characters — determines the quadratic lattice up to isometry? For
  graph carriers, does the corresponding invariant determine graph
  isomorphism, cycle-matroid equivalence, or a coarser relation?

- **Q4 — scale-dependent kernel geometry.** For which scales is the
  prime pairing conditionally negative definite, and for which scales
  is its saturation deficit positive semidefinite? Numerical evidence
  indicates that neither property holds uniformly in the scale, already
  on the rank-one prime set `{2,3,5}` at `s = 3/100`. Are the valid
  scale sets intervals with a critical threshold? Is there a natural
  centering or transform with negative type, or a different kernel
  whose geometry is stable across all scales?

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

- **Q6 — higher association and realizability.** The correct
  algebraic object is the symmetric mixed-difference hierarchy of
  `K` on the prime-exponent lattice: `Δ_{p₁}⋯Δ_{p_k}K` measures
  `k`-prime coupling. Rectangle identities and the characterization
  of vanishing cross-prime differences are formalization work, not
  open mathematics. Numerical evidence in rank one indicates that the
  three-prime difference at `2,3,5` changes sign with the scale, so
  the relevant structure is a system of sign chambers rather than a
  uniform alternating-sign law. Which asymptotic regimes and
  inequalities survive beyond pairwise correlation, and which mixed
  Hessians are realizable by lattice theta functions? Because `K` is
  an intersection surprisal rather than an entropy, entropic-cone
  membership is a separate representation problem.

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
