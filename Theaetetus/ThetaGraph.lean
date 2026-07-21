import Theaetetus.IncidenceGraph

/-! # The Theta Graph: incidence data (topology layer)

The subdivided theta graph `K₂,₃` — two junction vertices joined by
three internal-vertex paths — as **pure incidence data**: edge maps,
the graph, the two integral basis cycles sharing a path, and the raw
topological facts about them (lattice membership, real spanning,
integral spanning, independence of the casts), all stated through the
substrate's `IncidenceGraph.boundary` — no specialized boundary
operator, no basis structure (the lattice basis `thetaLatticeBasis`
is assembled from these facts in `GraphInstances.lean` via
`IncidenceGraph.basisOfCycles`).

Everything priced lives downstream: the chain Gram `!![4, 2; 2, 4]`,
its positive-definiteness and inverse, and the hexagonal energy are
**harmonic** content and live in `RankTwo.lean`. -/

namespace Theaetetus

open scoped BigOperators

/-! ## The subdivided theta graph `K₂,₃`

Vertices: `0 = u`, `1 = v` (junctions), `2, 3, 4` (path interiors).
Edges (all oriented junction-to-junction): `e₀ : u→a₁`, `e₁ : a₁→v`,
`e₂ : u→a₂`, `e₃ : a₂→v`, `e₄ : u→a₃`, `e₅ : a₃→v`. Cycle basis
`c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`. -/

section Theta

/-- Edge sources in `K₂,₃`. -/
def thetaSrc : Fin 6 → Fin 5 := ![0, 2, 0, 3, 0, 4]

/-- Edge targets in `K₂,₃`. -/
def thetaTgt : Fin 6 → Fin 5 := ![2, 1, 3, 1, 4, 1]

/-- The theta graph `K₂,₃` as an incidence graph. -/
@[reducible] def thetaGraph : IncidenceGraph :=
  { V := Fin 5
    E := Fin 6
    src := thetaSrc
    tgt := thetaTgt }

/-- The integral basis cycles: `c₁ = p₁ − p₃` and `c₂ = p₂ − p₃`. -/
def thetaCyclesZ : Fin 2 → Fin 6 → ℤ :=
  ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]

/-- The basis cycles, cast to `ℝ` (the closed forms downstream compute
against these literals). -/
noncomputable def thetaCycles : Fin 2 → Fin 6 → ℝ :=
  ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]

/-- The real cycles are the casts of the integral ones. -/
theorem thetaCycles_eq_cast (i : Fin 2) (e : Fin 6) :
    thetaCycles i e = ((thetaCyclesZ i e : ℤ) : ℝ) := by
  fin_cases i <;> fin_cases e <;> norm_num [thetaCycles, thetaCyclesZ]

/-- The theta graph's substrate boundary, in explicit-sum form. -/
theorem thetaGraph_boundary_eq_sum {R : Type*} [CommRing R]
    (ω : Fin 6 → R) (w : Fin 5) :
    thetaGraph.boundary ω w
      = ∑ e, ((if thetaTgt e = w then (1 : R) else 0)
        - (if thetaSrc e = w then (1 : R) else 0)) * ω e := rfl

/-- The basis vectors are integral cycles: they lie in the cycle
lattice `H₁(K₂,₃; ℤ)`. -/
theorem thetaCyclesZ_mem (i : Fin 2) :
    thetaCyclesZ i ∈ thetaGraph.cycleLattice := by
  rw [IncidenceGraph.mem_cycleLattice]
  intro w
  rw [thetaGraph_boundary_eq_sum]
  fin_cases i <;> fin_cases w <;> decide


/-- **The cycle space is exactly the span of the basis** (`b₁ = 2`):
a cochain with vanishing boundary is determined by its flows on the
first and second paths, as a combination of `c₁` and `c₂`. Flow
conservation at each interior vertex equalizes the two edges of each
path; conservation at the junction forces the third path's flow to be
minus the sum of the first two. -/
theorem eq_comb_of_theta_boundary_eq_zero (ω : Fin 6 → ℝ)
    (h : ∀ w, thetaGraph.boundary ω w = 0) :
    ω = fun e => ω 0 * thetaCycles 0 e + ω 2 * thetaCycles 1 e := by
  have h0 := h 0
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rw [thetaGraph_boundary_eq_sum] at h0 h2 h3 h4
  simp +decide [thetaSrc, thetaTgt, Fin.sum_univ_six] at h0 h2 h3 h4
  funext e
  fin_cases e <;> simp +decide [thetaCycles] <;> linarith


/-- **Independence of the casts**: a real dependency among the cast
basis cycles vanishes — read off the flows on the first and second
paths. -/
theorem theta_cast_independent (x : Fin 2 → ℝ)
    (hx : (fun e => ∑ i, x i * ((thetaCyclesZ i e : ℤ) : ℝ)) = 0) :
    x = 0 := by
  have h0 := congrFun hx 0
  have h2 := congrFun hx 2
  simp +decide [thetaCyclesZ, Fin.sum_univ_two] at h0 h2
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h2

/-- **Integral spanning**: an integral cycle is an *integer*
combination of the basis — the period lattice is the full integral
cycle lattice, not a finite-index sublattice. Feeds
`IncidenceGraph.basisOfCycles` in `GraphInstances.lean`. -/
theorem theta_integral_spanning (x : Fin 6 → ℤ)
    (hx : x ∈ thetaGraph.cycleLattice) :
    ∃ a : Fin 2 → ℤ, x = fun e => ∑ i, a i * thetaCyclesZ i e := by
  have hclosed : ∀ w, thetaGraph.boundary (fun e => ((x e : ℤ) : ℝ)) w = 0 := by
    intro w
    rw [thetaGraph.boundary_castR,
      (IncidenceGraph.mem_cycleLattice _ |>.mp hx) w, Int.cast_zero]
  have hr := eq_comb_of_theta_boundary_eq_zero (fun e => ((x e : ℤ) : ℝ)) hclosed
  refine ⟨![x 0, x 2], ?_⟩
  funext e
  apply Int.cast_injective (α := ℝ)
  have he := congrFun hr e
  rw [he]
  push_cast
  rw [Fin.sum_univ_two]
  show ((x 0 : ℤ) : ℝ) * thetaCycles 0 e + ((x 2 : ℤ) : ℝ) * thetaCycles 1 e
    = ((x 0 : ℤ) : ℝ) * ((thetaCyclesZ 0 e : ℤ) : ℝ)
      + ((x 2 : ℤ) : ℝ) * ((thetaCyclesZ 1 e : ℤ) : ℝ)
  rw [thetaCycles_eq_cast, thetaCycles_eq_cast]

end Theta

end Theaetetus
