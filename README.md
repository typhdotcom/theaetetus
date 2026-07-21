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
  Q1's frontier is failure of orthogonal diagonalization into
  rank-one summands, not rank.
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
which is why the all-scale sign proofs pass through the Jacobi
duality `θ(π²/α) = √(α/π)·θ(α)` before closing on rational
arithmetic. The classification needs less: modal concentration at
large resolution, no duality.

## The questions

- **Q1 — the sign.** `D_L < 0` at every incomparable pair, for
  every **positive-rank** positive-definite `L` (rank zero is
  Euler-factorizable, by Q3). Rank one: **done**. Diagonal forms,
  every rank ≥ 1: **done**. On every nontrivial partition tower the
  sign eventually holds along the staircase; at every pair it is
  open beyond one rank-two witness — the frontier is forms with no
  orthogonal splitting into rank-one summands.
- **Q2 — the pairing on primes.** Closed forms and asymptotics
  beyond saturation; and what geometric structure the pairing
  carries — whether it is conditionally negative definite, hence a
  squared Hilbert distance between primes, or whether its
  saturation deficit `log θ(s) − ⟨p,q⟩` is a positive-semidefinite
  similarity kernel. (The pairing itself is not one: `⟨p,p⟩ = 0`
  (`defect_self`) with positive off-diagonal makes every `2×2`
  principal block indefinite.) Until such a theorem exists it is a symmetric
  association statistic, not a linking form. Two-sided bounds and
  the saturation limit: done.
- **Q3 — Euler-factorizable carriers.** **Classified.** Abstractly:
  a partition tower's defect vanishes identically iff its modal
  sector is the only sector. Instantiated: for every positive-definite
  lattice action, and for every graph carrier (`D ≡ 0` iff
  `b₁ = 0`). The classification does not settle the per-pair kernel
  on a nontrivial carrier — Q1 would force it to be exactly the
  chain relation, as it is on `C₃`. Remaining for general lattices:
  the residue-complexity reading — deriving the cross-ratio law
  from honest residue actions on `L ⧸ qL`, as the graph carriers
  do, rather than defining the defect by it.
- **Q4 — the inverse problem.** The scalar defect factors through
  the theta function, so theta-equivalent lattices have identical
  defect matrices — theta-equivalence is an unavoidable
  identification, and no unrestricted scalar Torelli theorem is
  possible. The honest questions: what theta
  data does the defect matrix recover, and what residue-refined
  enhancement — the coset masses over `L ⧸ qL`, or their finite
  Fourier transform — sees beyond it? Untouched.
- **Q5 — the structural shape.** (a) `K` is normalized, monotone
  along divisibility, and submodular over `gcd`/`lcm` — strictly
  off chains (`resComplexity_strictSubmodular`); restricted to squarefree
  support this is the polymatroid shape, though that set-function
  restriction is not itself formalized. `K` is a surprisal, not an
  entropy, and
  nothing yet places these restrictions in the entropic cone; the
  honest questions are whether they are (almost) entropic, and
  which inequalities beyond submodularity they satisfy. (b) The
  higher interaction structure. An earlier version of this question
  asked for `D` as a 2-cocycle on the order complex; that question
  was badly posed and is retired — `D` is symmetric and vanishes on
  chains (`defect_comm`, `defect_eq_zero_of_dvd`), the wrong shape
  for an alternating cochain on a complex built from chains. The
  right object is the symmetric discrete mixed Hessian of `K` on
  the prime-exponent lattice, with higher mixed differences
  `Δ_{p₁}⋯Δ_{p_k} K` measuring `k`-prime coupling. Its algebra —
  rectangle identities from commuting differences, and the kernel
  characterization (all cross-prime differences vanish iff `K` is a
  constant plus one-prime terms) — is the next formalization layer,
  not open mathematics. The open questions begin after it: signs
  and total positivity of the higher differences, inequalities
  beyond pairwise submodularity, and which Hessians lattice theta
  functions can realize.

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
