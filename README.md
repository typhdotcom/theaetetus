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
`θ(α) = ∑_{k∈ℤ} e^{−αk²}`. For a resolution `q ≥ 1` the **residue
action** is the Gibbs structure induced on `L ⧸ qL`, and `K(q)` its
complexity (log partition function). **The seed**: the defect of a
pair of resolutions is the four-term inclusion–exclusion over the
divisibility lattice,

    D(q, q′) := [K(lcm) + K(gcd)] − [K(q) + K(q′)].

`D ≡ 0` would say `q ↦ K(q)` is a valuation — the algebraic shadow
of an Euler product, the resolution tower localizing over the
primes. It never is, unless there is nothing to couple: a carrier's
defect matrix vanishes identically **iff** its cycle lattice is
trivial (`towerDefect_forall_eq_zero_iff`). Wherever there is
geometry, the primes couple through it — and wherever the sign is
proved, it is negative.

## The theorems

- **The cross-ratio law.** On the cycle lattice `H¹(G;ℤ)` of any
  finite multigraph with its harmonic energy,
  `D(q,q′) = log [Z(q²)·Z(q′²) / (Z(gcd²)·Z(lcm²))]` — squares of
  resolutions forced by quadratic energy (`crossRatio_law`).
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
  `defect_eq_zero_iff`), and residue complexity is a strictly
  submodular rank function on the divisibility lattice
  (`resComplexity_strictSubmodular`).
- **The sign, diagonal forms, every rank.** Orthogonal sums add
  defects, so every positive diagonal form inherits the rank-one
  sign in every rank ≥ 1: strictly negative off chains, zero on
  them (`diagDefect_neg_of_incomparable`, `diagDefect_eq_zero_iff`).
  Q1's frontier is indecomposability — cross terms — not rank.
- **The classification.** The Euler-factorizable carriers are
  exactly those with trivial cycle lattice
  (`towerDefect_forall_eq_zero_iff`): at large resolution only the
  modal class survives (`tendsto_classScaledPartFn_atTop`), so on
  any carrier with a cycle the defect converges along the staircase
  `(n+1, n+2)` to `−log Z(1) < 0` and is eventually strictly
  negative (`tendsto_towerDefect_succ`, `eventually_towerDefect_neg`).
- **The prime pairing, rank one.** `⟨p,q⟩ := −D` is strictly
  positive for distinct primes and saturates at the base complexity
  `log θ(s)` along coprime pairs at infinity (`pairing_pos`,
  `tendsto_pairing`); the carrier-level analogue is the staircase
  limit `−log Z(1)` in the classification.
- **Rank two.** On the theta graph the cycle Gram inverts to the
  hexagonal form `(a² − ab + b²)/3`, and the defect is strictly
  negative at `(2,3)` (`thetaGraph_towerDefect_neg`), through the
  factorization `hexTheta s ≤ θ(s/3)·θ(s/4)`.

Why there is a sign at all: in the continuum limit the Gaussian
factors exactly and the defect vanishes with it. Everything here
lives in the Poisson-summation corrections the continuum forgets —
which is why the all-scale sign proofs pass through the Jacobi
duality `θ(π²/α) = √(α/π)·θ(α)` before closing on rational
arithmetic. The classification needs less: modal concentration at
large resolution, no duality.

## The questions

- **Q1 — the sign.** `D_L < 0` at every incomparable pair for every
  positive-definite `L`. Rank one: **done**. Diagonal forms, every
  rank: **done**. On every carrier the sign holds asymptotically
  along the staircase; at every pair it is open beyond one rank-two
  witness — the frontier is cross terms.
- **Q2 — the pairing on primes.** Closed forms and asymptotics
  beyond saturation; and what would earn the pairing a geometric
  name — conditional negative definiteness of the centered pairing
  matrix, or a Hilbert-space embedding of the primes. Until such a
  theorem exists it is a correlation kernel, not a linking form.
  Two-sided bounds and the saturation limit: done.
- **Q3 — Euler-factorizable carriers.** **Classified**, for every
  carrier in the formalized class: `D ≡ 0` iff the cycle lattice is
  trivial (`b₁ = 0`). The classification does not settle the
  per-pair kernel on a nontrivial carrier — Q1 would force it to be
  exactly the chain relation, as it is on `C₃`. The general
  positive-definite lattice awaits its carrier object.
- **Q4 — the inverse problem.** What does the defect matrix know
  about `L`? A torsion-level Torelli question. Untouched.
- **Q5 — the structural shape.** (a) On squarefree support `K`
  restricts to a strictly submodular set function — the polymatroid
  axioms are proved. But `K` is a surprisal, not an entropy, and
  nothing yet places these restrictions in the entropic cone; the
  honest questions are whether they are (almost) entropic, and
  which inequalities beyond submodularity they satisfy. (b) The
  higher interaction structure. An earlier version of this question
  asked for `D` as a 2-cocycle on the order complex; that question
  was badly posed and is retired — `D` is symmetric and vanishes on
  chains (`defect_comm`, `defect_eq_zero_of_dvd`), the wrong shape
  for an alternating cochain on a complex built from chains. The
  right object is the symmetric discrete mixed Hessian of `K` on
  the prime-exponent lattice, with its higher mixed differences
  `Δ_{p₁}⋯Δ_{p_k} K` measuring `k`-prime coupling: rectangle
  identities, sign structure, and the kernel modulo one-prime
  effects are open.

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

Built in seven milestones, `M0`–`M6` (labels that still appear in
docstrings): scaffold; the scalar core and chain-vanishing; the
witness `θ(4/3)·θ(3) < θ(1/3)·θ(12)`; the sign at `(2,3)` for all
scales; the carrier — graph homology, the residue tower, the
cross-ratio law, the rank-two witness; outward — Q1 closed at rank
one, the pairing, the rank function, the kernel on `C₃`; the
reconciliation — the defect as conditional association, the sign
for diagonal forms in every rank, Q3 classified for every carrier.
