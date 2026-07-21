# Theaetetus

*The arithmetic of coupled resolutions*

> The lines which form the sides of the oblong numbers we called
> *powers*, as not commensurable with the others in length, but only
> in the plane areas they have the power to form.
> — Plato, *Theaetetus* 147e–148b (adapted)

---

## Origin

This project grows from a single theorem carried out of **Meno**
(`~/dev/meno`), a Lean 4 formalization of structural
geometrodynamics. Meno proved, as face G3 of a larger program, that
an information-theoretic coupling defect on a tower of arithmetic
resolutions is exactly a cross-ratio of theta values — vanishing
along divisibility chains, strictly nonzero at an incomparable pair.
Inside Meno that theorem served a thesis about self-describing
universes. Here it is the whole subject.

Theaetetus is **not** a physics program. The words "gravity",
"matter", and "universe" stay behind in Meno. The object of study is
the defect itself: a function on pairs of the divisibility lattice,
attached to any positive-definite integral quadratic form, that
measures the failure of the form's spectrum to factor over the
primes.

**Relation to Meno, stated once**: agents working here may read
`~/dev/meno` freely and copy proofs verbatim (with a `-- ported from
Meno/<file>` header comment). Beyond copying, total isolation — no
lake dependency on Meno, no imports from it, no syncing changes in
either direction, no adoption of its physical vocabulary. Meno is a
quarry, not an upstream.

---

## The seed

Let `θ(α) := ∑_{k ∈ ℤ} exp(−α·k²)` (Meno's `scalarPartFn`), and more
generally let `Z_L(β)` be the Boltzmann sum of a positive-definite
quadratic form on a finite-rank lattice `L`, at inverse temperature
`β`. For a resolution `q ≥ 1`, the **residue action** is the
Gibbs-weighted structure induced on `L ⧸ qL`, and `K(q)` denotes its
complexity (log partition function). For resolutions `q, q′` define
**the defect**

    D(q, q′) := [K(lcm(q,q′)) + K(gcd(q,q′))] − [K(q) + K(q′)].

Meno proved, on the cycle lattice `H¹(G;ℤ)` of an arbitrary finite
multigraph with its harmonic energy:

1. **The key lemma** (`residueWeight_zero_eq_classScaledPartFn`,
   `Meno/TowerGravity.lean:99`). The modal coset weight at
   resolution `q` is the `q²`-scaled partition function:
   `W_q(0) = Z(q²)`. The fiber of zero is `q·L`, enumerated from `L`
   by multiplication by `q`, and the energy is quadratic — squares
   of resolutions are forced, not chosen.

2. **The cross-ratio law** (`residue_gravity_crossRatio`,
   `Meno/TowerGravity.lean:159`). The defect is a cross-ratio of
   scaled partition functions:

       D(q, q′) = log [ Z(q²) · Z(q′²) / ( Z(gcd²) · Z(lcm²) ) ].

3. **The boundary** (`residue_gravity_dvd`,
   `Meno/TowerGravity.lean:204`). Along a divisibility chain
   (`q ∣ q′`) the defect vanishes identically.

4. **The coupling reading** (`h1ReductionCRT`,
   `Meno/TowerGravity.lean`). Chinese remainder on the tower: the
   `lcm`-resolution **is** the fiber product of the `q`- and
   `q′`-resolutions over their common coarsening at the `gcd`. So
   `D` is the defect of a genuine coupling — the four-term
   inclusion–exclusion of description costs over a shared base.

5. **The strictness witness** (`cycle3_crossRatio_neg`,
   `Meno/TowerGravity.lean:509`, engine
   `scalarPartFn_crossRatio_lt` at `:414`). On the cycle graph `C₃`
   (rank one, energy `k²/3`) at the incomparable pair `(2, 3)`:

       D(2, 3) < 0,  i.e.  θ(4/3)·θ(3) < θ(1/3)·θ(12),

   proved by partial sums against geometric tails, closed by
   rational arithmetic.

6. **The cumulant form** (`residue_gravity_crossRatio_cgf`,
   `Meno/TowerGravity.lean:177`). The defect is a four-term
   combination of cumulant-generating-functional evaluations at
   temperature-shift observables — the analytic handle for bounds.

---

## The reading

Write `h(q) := log Z(q²)`. The cross-ratio law says
`D(q,q′) = [h(q) + h(q′)] − [h(gcd) + h(lcm)]`. Three equivalent
readings of `D ≡ 0`:

- `h` is a **valuation** on the divisibility lattice
  (`h(x∧y) + h(x∨y) = h(x) + h(y)`);
- `Z(q²)` satisfies the **gcd/lcm functional equation**
  `f(q)·f(q′) = f(gcd)·f(lcm)` — the identity every multiplicative
  arithmetic function satisfies, the algebraic shadow of an **Euler
  product**;
- the resolution tower **localizes**: the description cost at `q`
  is the independent sum of its prime-power components.

The witness refutes all three on the smallest nontrivial carrier at
the smallest incomparable pair. The spectrum of a quadratic form
does not factor over the primes: **the primes couple through the
geometry, and the coupling has a sign.** At the witness the sign is
negative — `h` is strictly *supermodular* there, equivalently the
residue complexity `K` is strictly *submodular*: coupling two
incomparable resolutions saves strictly more than their shared
base.

The central object of this field is the defect matrix
`D_L : pairs of the divisibility lattice → ℝ`, as an invariant of
the lattice-with-form `L`.

---

## The questions

**Q1 — The sign.** Conjecture: for every positive-definite `L` and
every incomparable pair, `D_L(q, q′) < 0` — residue complexity is a
strictly submodular function on the divisibility lattice. Meno
proved one point of this. First target, rank one: for `s > 0` and
incomparable `q, q′`,

    θ(q²·s) · θ(q′²·s)  <  θ(gcd²·s) · θ(lcm²·s).

The witness is the case `s = 1/3, (q,q′) = (2,3)`. Prove it for all
`s` at `(2,3)`; then all incomparable pairs; then rank `≥ 2`
(Meno's theta graph is the natural first non-diagonal carrier).
Tools: the cumulant form, Jacobi transformation for small `s`,
first-mode domination for large `s`.

**Q2 — The pairing on primes.** For primes `p ≠ p′`,
`⟨p, p′⟩_L := −D_L(p, p′)` is a two-point function on primes
mediated by a geometry, conjecturally positive. Asymptotics in
`p, p′`; closed forms at rank one; dependence on `L`. Resonance to
test, not assume: arithmetic topology reads primes as knots with
linking numbers (Mazur; Morishita, *Knots and Primes*). Is there a
normalization of `⟨·,·⟩_L` with the behavior of a linking
invariant? Higher versions: define triple defects by
inclusion–exclusion over three resolutions and compare with Rédei's
triple symbol / Milnor invariants.

**Q3 — Euler-factorizable carriers.** Classify `L` with
`D_L ≡ 0`. Conjecture: only rank zero. A proof would isolate
exactly *why* positive-definite geometry obstructs localization.

**Q4 — The inverse problem.** What does the full defect matrix know
about `L`? Together with rank and discriminant, does it determine
the form up to equivalence — a torsion-level Torelli question? The
residue actions are theta functions with level structure in
information-theoretic dress; the graph case connects to tropical
Jacobians.

**Q5 — The structural shape.** Two candidate homes for the pattern
"vanishes on chains, strict off them":
(a) *entropy-region theory* — submodularity is the defining
inequality of polymatroids; is `q ↦ K(q)` a polymatroid-like rank
function on the divisibility lattice, and are there "non-Shannon"
defect inequalities beyond Q1?
(b) *lattice cohomology* — is `D` a 2-cocycle on the order complex
of the divisibility lattice, exact on chains, whose class is the
obstruction of Q3? Möbius inversion over the interval
`[gcd, lcm]` should organize the higher defects.

---

## Copy-map into Meno

What must be ported to state and re-prove the seed, with sources.
Port minimally: the rank-one program (Q1–Q2 first targets) needs
only the scalar layer, rows 1–2. The carrier rows wait until rank
`≥ 2` work begins.

| Layer | Declarations | Source |
| :--- | :--- | :--- |
| Analytic primitive | `SectorAction`, `weight`, `partFn`, `complexity`, `cgf` | `Meno/SectorAction.lean:35–80` |
| Scalar theta | `scalarPartFn` and its estimates (`scalarPartFn_gt_one`, tail bounds), duality if needed | `Meno/QuadraticAction.lean:302,405` |
| Graph substrate | `IncidenceGraph`, `cycleGraph` | `Meno/IncidenceGraph.lean` (`:578` for `cycleGraph`) |
| Carrier | `harmonicEnergy`; `classSectorAction`, `classScaledPartFn` | `Meno/HarmonicClass.lean:116`; `Meno/BasisIndependence.lean:236,499` |
| Residue tower | `H1Reduction`, `residueWeight`, `residueAction`, `h1TowerMap` | `Meno/ResolutionCount.lean:667,1283,1324,2018` |
| The seed itself | key lemma `:99`, law `:159`, cgf form `:177`, boundary `:204`, `h1ReductionCRT`, `cycle3_classScaledPartFn:458`, witness engine `:414` (private in Meno — republish here), witness `:509` | `Meno/TowerGravity.lean` |

Ported code keeps its proofs but takes this project's names (below).
Everything else in Meno — dualities, matter, binding, symmetry,
self-reference, the dichotomy — stays where it is.

---

## Vocabulary

Meno's physics names are retired on arrival. Standing renames:

| Meno | Theaetetus |
| :--- | :--- |
| `residue_gravity_crossRatio` | `crossRatio_law` (namespace `Theaetetus`) |
| gravity defect (tower) | **the defect**, `D` / `towerDefect` |
| "gravity is exact along chains" | "the defect vanishes on chains" |
| carrier / sector / resolution / tower | kept — these are neutral |

New program-native terms: *defect matrix*, *Euler-factorizable*,
*prime pairing* `⟨p, p′⟩_L`, *supermodular coupling*.

---

## Standards

- Lean 4, toolchain `leanprover/lean4:v4.26.0`, Mathlib pinned at
  `v4.26.0` (mirroring Meno's pins so proofs port verbatim; this
  repo owns its pins and may upgrade independently once the seed is
  re-proved).
- Zero `sorry`, zero `axiom` declarations. `lake build` green is
  the only definition of done.
- Where a desired statement fails, keep the counterexample as a
  theorem, in Meno's tradition.
- Version control is jujutsu (`jj status`, `jj diff --git`,
  `jj commit -m "..."`).

---

## Milestones

- **M0 — scaffold.** ✅ Lake package `Theaetetus` building green
  against the pinned Mathlib.
- **M1 — scalar core.** ✅ Port the analytic primitive and `θ`.
  Define the rank-one defect
  `D_s(q, q′) := log θ(q²s) + log θ(q′²s) − log θ(gcd²s) − log θ(lcm²s)`
  and prove chain-vanishing. (`SectorAction.lean`, `Theta.lean`,
  `Defect.lean`; Meno's `scalarPartFn` is `theta` here.)
- **M2 — the witness, at home.** ✅ Re-prove
  `θ(4/3)·θ(3) < θ(1/3)·θ(12)` and hence `D_{1/3}(2,3) < 0`.
  (`Witness.lean`: `theta_crossRatio_lt`, `defect_witness`.)
- **M3 — the first native theorem.** `D_s(2,3) < 0` for **all**
  `s > 0` — the birth certificate: a statement Meno never proved.
  ✅ (`Sign.lean`: `defect_two_three_neg`, via the duality
  involution `s ↔ π²/36s` — the prefactors cancel because
  `q·q′ = gcd·lcm` — plus geometric tails for `s ≥ 1/2`.)
  Then arbitrary incomparable pairs at rank one (Q1, rank one) —
  **open**; the same two-branch scheme is expected to generalize.
- **M4 — the carrier.** Port the graph layer; restate and re-prove
  the general cross-ratio law and the CRT coupling reading; first
  rank-two witnesses on the theta graph.
- **M5 — outward.** The prime pairing's asymptotics (Q2), the
  classification (Q3), and the structural shape (Q5).

---

This document is the charter. As theorems land, update it — the
questions may be replaced by better questions, but the isolation
rule and the standards section are permanent.
