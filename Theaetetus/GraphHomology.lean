import Theaetetus.IncidenceGraph
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Graph Homology: the pure topology layer

Everything a finite graph's first homology provides — lattice, basis,
exactness, quotient, and rank — in one file importing only the
substrate (no Gram object, no positive-definiteness, no matrix
inversion — the unit-edge Gram and every priced consequence live in
the priced layer, `Periods.lean`):

* freeness of `ℤ^E ⧸ H₁`, the splitting, and the retraction of `ℤ^E`
  onto the cycle lattice;
* **the derived data of an arbitrary lattice basis**
  `B : Module.Basis (Fin n) ℤ G.cycleLattice` (the presentation *is*
  the basis; every former field is a theorem):
  integer cycles `cyclesZ`, real casts `cyclesR`, closedness,
  coordinates `coordMap`, real independence `cast_independent`,
  integer potentials, period surjectivity (`ℤ` and `ℝ`), real
  spanning, exactness, and the keystone quotient equivalences over
  `ℤ` and `ℝ`;
* the **fundamental basis** `cycleBasis` (PID structure theorem):
  existence of a lattice basis for every finite graph,
  with nothing stored;
* the **real cycle-space rank** (`finrank_ker_boundaryLin`), **Euler's
  formula** (`b1_eq`), and the **spanning criterion**
  (`spanning_of_card_eq_b1`);
* `basisOfCycles` — the concrete-instance bridge: closed, independent,
  integrally spanning integer cycles assemble into a lattice basis.

Real spanning is proved by **scalar extension and dimension**:
rational independence transfers to `ℝ` through a cast
left inverse (`linearIndependent_ratCast`), the rational kernel is
spanned by the basis after clearing denominators, rank–nullity over
`ℚ` and `ℝ` pins the real kernel's dimension at `n`
(`finrank_ker_boundaryLin_eq`), and the independent cast basis fills
it. No Gram object, no cycle-cycle pairing operator, no self-duality
— what remains of the metric is period evaluation and the discrete
Stokes identity. -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-! ## Freeness of the cochain quotient, the splitting, the retraction

`H₁(G;ℤ) = ker ∂ℤ` is saturated (`mem_of_smul_mem`,
`IncidenceGraph.lean`), so `ℤ^E ⧸ H₁` is torsion-free, hence free,
hence projective — the quotient map splits and `ℤ^E` retracts onto the
cycle lattice. -/

instance : NoZeroSMulDivisors ℤ ((G.E → ℤ) ⧸ G.cycleLattice) := by
  refine ⟨fun {c x} h => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · refine Or.inr ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rw [Submodule.Quotient.mk_eq_zero]
    exact G.mem_of_smul_mem hc h

instance : Module.Finite ℤ ((G.E → ℤ) ⧸ G.cycleLattice) :=
  Module.Finite.of_surjective G.cycleLattice.mkQ
    (Submodule.Quotient.mk_surjective _)

instance : Module.Free ℤ ((G.E → ℤ) ⧸ G.cycleLattice) :=
  Module.free_of_finite_type_torsion_free'

/-- A `ℤ`-linear section of the quotient map, from projectivity of
the free quotient. -/
noncomputable def quotSection :
    ((G.E → ℤ) ⧸ G.cycleLattice) →ₗ[ℤ] (G.E → ℤ) :=
  (Module.projective_lifting_property G.cycleLattice.mkQ LinearMap.id
    (Submodule.Quotient.mk_surjective _)).choose

theorem mkQ_comp_quotSection :
    G.cycleLattice.mkQ ∘ₗ G.quotSection = LinearMap.id :=
  (Module.projective_lifting_property G.cycleLattice.mkQ LinearMap.id
    (Submodule.Quotient.mk_surjective _)).choose_spec

/-- The retraction of `ℤ^E` onto the cycle lattice along the chosen
splitting. -/
noncomputable def cycleRetract : (G.E → ℤ) →ₗ[ℤ] (G.E → ℤ) :=
  LinearMap.id - G.quotSection ∘ₗ G.cycleLattice.mkQ

theorem cycleRetract_mem (x : G.E → ℤ) :
    G.cycleRetract x ∈ G.cycleLattice := by
  have h := LinearMap.congr_fun G.mkQ_comp_quotSection (G.cycleLattice.mkQ x)
  have hz : G.cycleLattice.mkQ (G.cycleRetract x) = 0 := by
    show G.cycleLattice.mkQ (x - G.quotSection (G.cycleLattice.mkQ x)) = 0
    rw [map_sub, show G.cycleLattice.mkQ (G.quotSection (G.cycleLattice.mkQ x))
        = G.cycleLattice.mkQ x from h, sub_self]
  rwa [← Submodule.ker_mkQ G.cycleLattice, LinearMap.mem_ker]

theorem cycleRetract_of_mem {x : G.E → ℤ} (hx : x ∈ G.cycleLattice) :
    G.cycleRetract x = x := by
  show x - G.quotSection (G.cycleLattice.mkQ x) = x
  rw [show G.cycleLattice.mkQ x = 0 from by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero],
    map_zero, sub_zero]

/-! ## Cast bookkeeping -/

private lemma cast_mulVec_apply {α : Type*} (M : Matrix α G.E ℤ)
    (x : G.E → ℤ) (i : α) :
    (((M *ᵥ x) i : ℤ) : ℝ)
      = ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun e => ((x e : ℤ) : ℝ))) i := by
  show ((∑ e, M i e * x e : ℤ) : ℝ) = ∑ e, (M i e : ℝ) * ((x e : ℤ) : ℝ)
  push_cast
  rfl

theorem cast_single {α : Type*} [DecidableEq α] (a j : α) :
    (((Pi.single a (1 : ℤ) : α → ℤ) j : ℤ) : ℝ)
      = (Pi.single a (1 : ℝ) : α → ℝ) j := by
  rcases eq_or_ne j a with h | h
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
    norm_num
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
    norm_num

/-! ## The derived data of an arbitrary lattice basis

The presentation **is** a basis `B : Module.Basis (Fin n) ℤ
G.cycleLattice`. Every datum a presentation could store is a theorem
of `B`: the integer cycles and their
real casts, closedness, independence, Gram positivity, integer
potentials, period surjectivity, spanning, exactness, and the keystone
quotient equivalences. Every basis automatically has `n = b₁`
(`card_eq_b1`). -/

section LatticeBasis

variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)

/-- The integer cycle vectors of a lattice basis, as cochains. -/
noncomputable def cyclesZ : Fin n → G.E → ℤ :=
  fun i => (B i : G.E → ℤ)

/-- The cycle vectors of a lattice basis, cast to `ℝ`. -/
noncomputable def cyclesR : Fin n → G.E → ℝ :=
  fun i e => ((G.cyclesZ B i e : ℤ) : ℝ)

theorem cyclesZ_mem (i : Fin n) : G.cyclesZ B i ∈ G.cycleLattice :=
  (B i).2

/-- The cast cycle vectors are closed. -/
theorem cyclesR_closed (i : Fin n) (v : G.V) :
    G.boundary (G.cyclesR B i) v = 0 := by
  have hmem := G.cyclesZ_mem B i
  rw [mem_cycleLattice] at hmem
  show G.boundary (fun e => ((G.cyclesZ B i e : ℤ) : ℝ)) v = 0
  rw [G.boundary_castR, hmem v, Int.cast_zero]

/-- Basis coordinates extended to the ambient lattice along the
retraction: the integer matrix `P` with `P Cᵀ = 1`. -/
noncomputable def coordMap : (G.E → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toLinearMap
    ∘ₗ B.repr.toLinearMap
    ∘ₗ LinearMap.codRestrict G.cycleLattice G.cycleRetract G.cycleRetract_mem

theorem coordMap_cyclesZ (i : Fin n) :
    G.coordMap B (G.cyclesZ B i) = Pi.single i 1 := by
  have hfix : LinearMap.codRestrict G.cycleLattice G.cycleRetract
      G.cycleRetract_mem (G.cyclesZ B i) = B i := by
    apply Subtype.ext
    show G.cycleRetract (G.cyclesZ B i) = (B i : G.E → ℤ)
    exact G.cycleRetract_of_mem (G.cyclesZ_mem B i)
  show (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))
      (B.repr (LinearMap.codRestrict G.cycleLattice G.cycleRetract
        G.cycleRetract_mem (G.cyclesZ B i))) = Pi.single i 1
  rw [hfix, Module.Basis.repr_self]
  funext j
  rcases eq_or_ne j i with h | h
  · subst h
    show Finsupp.single j (1 : ℤ) j = (Pi.single j 1 : Fin n → ℤ) j
    rw [Finsupp.single_eq_same, Pi.single_eq_same]
  · show Finsupp.single i (1 : ℤ) j = (Pi.single i 1 : Fin n → ℤ) j
    rw [Finsupp.single_eq_of_ne h, Pi.single_eq_of_ne h]

/-- The coordinate matrix of `coordMap` in the standard bases. -/
noncomputable def coordMatrix : Matrix (Fin n) G.E ℤ :=
  LinearMap.toMatrix' (G.coordMap B)

theorem coordMatrix_mulVec (x : G.E → ℤ) :
    G.coordMatrix B *ᵥ x = G.coordMap B x := by
  rw [coordMatrix, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- **Independence of the cast basis**, from the integer retraction:
a real dependency dies on applying the cast coordinate matrix. -/
theorem cast_independent (x : Fin n → ℝ)
    (hx : (fun e => ∑ i, x i * G.cyclesR B i e) = 0) : x = 0 := by
  have hPC : ∀ i : Fin n,
      ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) *ᵥ
        (fun e => ((G.cyclesZ B i e : ℤ) : ℝ)) = Pi.single i (1 : ℝ) := by
    intro i
    funext j
    rw [← G.cast_mulVec_apply, G.coordMatrix_mulVec, G.coordMap_cyclesZ]
    exact cast_single i j
  have hlin : ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) *ᵥ
      (fun e => ∑ i, x i * G.cyclesR B i e) = fun j => x j := by
    funext j
    show ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
        * (∑ i, x i * G.cyclesR B i e) = x j
    calc ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
          * (∑ i, x i * G.cyclesR B i e)
        = ∑ e, ∑ i, x i * (((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, x i * (((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e) := Finset.sum_comm
      _ = ∑ i, x i * ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, x i * (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact congrFun (hPC i) j
      _ = x j := by
          rw [show (fun i => x i * (Pi.single i (1 : ℝ) : Fin n → ℝ) j)
              = fun i => if j = i then x i else 0 from funext fun i => by
            rcases eq_or_ne j i with h | h
            · subst h
              rw [if_pos rfl, Pi.single_eq_same, mul_one]
            · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
          rw [Finset.sum_ite_eq Finset.univ j x]
          simp
  rw [hx, Matrix.mulVec_zero] at hlin
  funext j
  exact (congrFun hlin j).symm

/-- **Vanishing periods kill closed-walk sums** — over any commutative
ring. The chain of a closed walk lies in the cycle lattice; expanding
it in the basis reduces its pairing to the vanishing periods. -/
theorem closedWalkSum_eq_zero {R : Type*} [CommRing R] (ω : G.E → R)
    (hper : ∀ j, ω ⬝ᵥ (fun e => ((G.cyclesZ B j e : ℤ) : R)) = 0)
    {w : G.V} (c : G.Walk w w) : c.sum ω = 0 := by
  rw [Walk.sum_eq_dotProduct]
  have hmem : c.chain ℤ ∈ G.cycleLattice := G.chain_mem_cycleLattice c
  have hexp := B.sum_repr ⟨c.chain ℤ, hmem⟩
  have hcoe : ∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i
      = c.chain ℤ := by
    have hval := congrArg Subtype.val hexp
    rw [AddSubmonoidClass.coe_finset_sum] at hval
    exact hval
  have hcast : ∀ e, c.chain R e
      = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.cyclesZ B i e : ℤ) : R) := by
    intro e
    rw [← Walk.chain_cast c e, ← congrFun hcoe e]
    show (((∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i) e
        : ℤ) : R) = _
    rw [show (∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i) e
        = ∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i * G.cyclesZ B i e from by
      rw [Finset.sum_apply]
      rfl]
    push_cast
    rfl
  calc ω ⬝ᵥ c.chain R
      = ∑ e, ω e * ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.cyclesZ B i e : ℤ) : R) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hcast e]
    _ = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R) := by
        calc ∑ e, ω e * ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
              * ((G.cyclesZ B i e : ℤ) : R)
            = ∑ e, ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.cyclesZ B i e : ℤ) : R)) := by
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ i, ∑ e, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.cyclesZ B i e : ℤ) : R)) := Finset.sum_comm
          _ = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * ∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [show (∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R))
            = ω ⬝ᵥ (fun e => ((G.cyclesZ B i e : ℤ) : R)) from rfl,
          hper i, mul_zero]

/-- **Integral potentials, derived**: vanishing periods against the
basis yield an integer potential, by walk integration. -/
theorem integral_potentials (ω : G.E → ℤ)
    (h : ∀ j, ω ⬝ᵥ G.cyclesZ B j = 0) :
    ∃ g : G.V → ℤ, G.grad g = ω := by
  have hper : ∀ j, ω ⬝ᵥ (fun e => ((G.cyclesZ B j e : ℤ) : ℤ)) = 0 := by
    intro j
    rw [show (fun e => ((G.cyclesZ B j e : ℤ) : ℤ)) = G.cyclesZ B j from
      funext fun e => Int.cast_id]
    exact h j
  exact ⟨G.integrate ω,
    G.grad_integrate ω (fun w c => G.closedWalkSum_eq_zero B ω hper c)⟩

/-- **Integer period surjectivity, derived**: `τ := Pᵀ k` realizes any
prescribed integer periods, `P` the coordinate matrix. -/
theorem periods_onto (k : Fin n → ℤ) :
    ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ G.cyclesZ B j = k j := by
  refine ⟨fun e => ∑ i, G.coordMatrix B i e * k i, fun j => ?_⟩
  have hPC : ∀ i, (G.coordMatrix B *ᵥ G.cyclesZ B j) i
      = (Pi.single j (1 : ℤ) : Fin n → ℤ) i := by
    intro i
    rw [G.coordMatrix_mulVec, G.coordMap_cyclesZ]
  show ∑ e, (∑ i, G.coordMatrix B i e * k i) * G.cyclesZ B j e = k j
  calc ∑ e, (∑ i, G.coordMatrix B i e * k i) * G.cyclesZ B j e
      = ∑ e, ∑ i, k i * (G.coordMatrix B i e * G.cyclesZ B j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ e, k i * (G.coordMatrix B i e * G.cyclesZ B j e) :=
        Finset.sum_comm
    _ = ∑ i, k i * ∑ e, G.coordMatrix B i e * G.cyclesZ B j e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, k i * (Pi.single j (1 : ℤ) : Fin n → ℤ) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact hPC i
    _ = k j := by
        rw [show (fun i => k i * (Pi.single j (1 : ℤ) : Fin n → ℤ) i)
            = fun i => if i = j then k i else 0 from funext fun i => by
          rcases eq_or_ne i j with h | h
          · subst h
            rw [if_pos rfl, Pi.single_eq_same, mul_one]
          · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j k]
        simp

/-! ### Stokes and exactness -/

/-- Real Stokes: gradients have vanishing periods against the cast
basis. -/
theorem grad_period (f : G.V → ℝ) (i : Fin n) :
    G.grad f ⬝ᵥ G.cyclesR B i = 0 := by
  rw [G.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by
    rw [G.cyclesR_closed B i v, mul_zero]

/-- Integer Stokes: integer gradients have vanishing integer periods. -/
theorem gradZ_period (g : G.V → ℤ) (j : Fin n) :
    G.grad g ⬝ᵥ G.cyclesZ B j = 0 := by
  rw [G.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by
    rw [(G.mem_cycleLattice.mp (G.cyclesZ_mem B j)) v, mul_zero]

/-- **Exactness**: a cochain has vanishing periods against the cast
basis iff it is a gradient. No connectivity hypothesis — connectivity
controls uniqueness of the potential, never existence. Forward
direction by the walk engine: vanishing periods kill closed-walk sums,
so integration from component basepoints produces a potential. -/
theorem period_eq_zero_iff_exists_grad (ω : G.E → ℝ) :
    (∀ i, ω ⬝ᵥ G.cyclesR B i = 0) ↔ ∃ f : G.V → ℝ, G.grad f = ω := by
  constructor
  · intro hper
    exact ⟨G.integrate ω,
      G.grad_integrate ω (fun w c =>
        G.closedWalkSum_eq_zero B ω (fun j => hper j) c)⟩
  · rintro ⟨f, rfl⟩ i
    exact G.grad_period B f i

/-! ### The keystone quotient equivalences -/

/-- The integer period map of a lattice basis. -/
noncomputable def periodLinZ : (G.E → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun ω := fun j => ω ⬝ᵥ G.cyclesZ B j
  map_add' ω η := funext fun j => add_dotProduct ω η (G.cyclesZ B j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (G.cyclesZ B j)

/-- Lattice exactness: the kernel of the integer period map is exactly
the image of the integer gradient. -/
theorem range_gradLinZ_eq_ker_periodLinZ :
    LinearMap.range (G.gradLin ℤ) = LinearMap.ker (G.periodLinZ B) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact G.gradZ_period B g j
  · intro h
    exact G.integral_potentials B ω (fun j => congrFun h j)

theorem periodLinZ_surjective : Function.Surjective (G.periodLinZ B) := by
  intro k
  obtain ⟨ω, hω⟩ := G.periods_onto B k
  exact ⟨ω, funext hω⟩

/-- **THE KEYSTONE, ℤ-form**: integer descriptions modulo integer
local re-description are exactly the period lattice `ℤ^n` — through
any lattice basis. The quotient depends only on the graph. -/
noncomputable def latticeQuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (Submodule.quotEquivOfEq _ _ (G.range_gradLinZ_eq_ker_periodLinZ B)).trans
    ((G.periodLinZ B).quotKerEquivOfSurjective (G.periodLinZ_surjective B))

/-- The keystone coordinates of a class, on representatives. -/
theorem latticeQuotEquiv_mk (τ : G.E → ℤ) :
    G.latticeQuotEquiv B (Submodule.Quotient.mk τ)
      = fun j => τ ⬝ᵥ G.cyclesZ B j := rfl

include B in
/-- **Every lattice basis has exactly `b₁` elements** — the rank is
never a choice. -/
theorem card_eq_b1 : n = G.b1 := by
  have h := Module.finrank_eq_card_basis B
  rw [Fintype.card_fin] at h
  exact h.symm

end LatticeBasis

/-! ## The fundamental basis: existence for every finite graph

Nothing is stored: the PID structure theorem produces a
basis of the cycle lattice; `cycleBasisSigma_fst` proves the
construction meets the intrinsic invariant `b₁`. -/

/-- The chosen basis package of the cycle lattice, via the PID
structure theorem. -/
noncomputable def cycleBasisSigma :
    (m : ℕ) × Module.Basis (Fin m) ℤ G.cycleLattice :=
  Submodule.basisOfPid (Pi.basisFun ℤ G.E) G.cycleLattice

/-- **The construction meets the intrinsic invariant**: the PID basis
of the cycle lattice has exactly `b₁ = finrank ℤ H₁(G;ℤ)` elements. -/
theorem cycleBasisSigma_fst : G.cycleBasisSigma.1 = G.b1 :=
  G.card_eq_b1 G.cycleBasisSigma.2

/-- **The fundamental basis of `H₁(G;ℤ)`** — every finite incidence
graph carries a lattice basis, indexed by the intrinsic `b₁`. This is
the fundamental-presentation theorem in basis form: every former
presentation field is a theorem of this object. -/
noncomputable def cycleBasis : Module.Basis (Fin G.b1) ℤ G.cycleLattice :=
  G.cycleBasisSigma.2.reindex (finCongr G.cycleBasisSigma_fst)

/-- The fundamental integer cycles, as cochains. -/
noncomputable def fundCyclesZ : Fin G.b1 → G.E → ℤ :=
  G.cyclesZ G.cycleBasis

/-- The fundamental cycles, cast to `ℝ`. -/
noncomputable def fundCyclesR : Fin G.b1 → G.E → ℝ :=
  G.cyclesR G.cycleBasis

/-- **Intrinsic `H¹` coordinates for every finite graph**: integer
cochains modulo integer gradients are `ℤ^{b₁}`,
through the fundamental basis. -/
noncomputable def h1QuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin G.b1 → ℤ) :=
  G.latticeQuotEquiv G.cycleBasis

/-- `H¹(G;ℤ)` is finite free — through the intrinsic coordinates. -/
instance : Module.Free ℤ ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  Module.Free.of_equiv G.h1QuotEquiv.symm

instance : Module.Finite ℤ ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  Module.Finite.equiv G.h1QuotEquiv.symm

/-- The intrinsic `H¹` coordinates of a class, on representatives. -/
theorem h1QuotEquiv_mk (τ : G.E → ℤ) :
    G.h1QuotEquiv (Submodule.Quotient.mk τ)
      = fun j => τ ⬝ᵥ G.fundCyclesZ j := rfl

/-! ## Building a basis from integral cycle data

The concrete-instance bridge: a family of integer cycles that is
closed, real-independent after casting, and integrally spanning
assembles into a lattice basis — from which everything else is
derived, including its own count `r = b₁`. -/

/-- Assemble a lattice basis from closed, independent, integrally
spanning integer cycles. -/
noncomputable def basisOfCycles {r : ℕ} (c : Fin r → G.E → ℤ)
    (hmem : ∀ i, c i ∈ G.cycleLattice)
    (hindep : ∀ x : Fin r → ℝ,
      (fun e => ∑ i, x i * ((c i e : ℤ) : ℝ)) = 0 → x = 0)
    (hspan : ∀ x, x ∈ G.cycleLattice →
      ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e) :
    Module.Basis (Fin r) ℤ G.cycleLattice := by
  have hli : LinearIndependent ℤ
      (fun i => (⟨c i, hmem i⟩ : G.cycleLattice)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hval := congrArg Subtype.val hg
    rw [AddSubmonoidClass.coe_finset_sum] at hval
    have hcast : (fun e => ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ)) = 0 := by
      funext e
      have he := congrFun hval e
      rw [Finset.sum_apply] at he
      have heZ : ∑ i, g i * c i e = 0 := he
      show ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ) = 0
      calc ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ)
          = ((∑ i, g i * c i e : ℤ) : ℝ) := by push_cast; rfl
        _ = 0 := by rw [heZ, Int.cast_zero]
    have hgz := hindep (fun i => (g i : ℝ)) hcast
    intro i
    have hz : ((g i : ℤ) : ℝ) = 0 := congrFun hgz i
    exact_mod_cast hz
  have hsp : ⊤ ≤ Submodule.span ℤ
      (Set.range fun i => (⟨c i, hmem i⟩ : G.cycleLattice)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha⟩ := hspan x hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    funext e
    rw [Finset.sum_apply]
    exact (congrFun ha e).symm
  exact Module.Basis.mk hli hsp

/-- The assembled basis's integer cycles are the given family. -/
theorem cyclesZ_basisOfCycles {r : ℕ} (c : Fin r → G.E → ℤ)
    (hmem : ∀ i, c i ∈ G.cycleLattice)
    (hindep : ∀ x : Fin r → ℝ,
      (fun e => ∑ i, x i * ((c i e : ℤ) : ℝ)) = 0 → x = 0)
    (hspan : ∀ x, x ∈ G.cycleLattice →
      ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e) :
    G.cyclesZ (G.basisOfCycles c hmem hindep hspan) = c := by
  funext i
  show ((G.basisOfCycles c hmem hindep hspan) i : G.E → ℤ) = c i
  rw [basisOfCycles, Module.Basis.mk_apply]

/-- The `H¹` basis a cycle-lattice basis induces: the standard basis
of `ℤⁿ` pulled back along the keystone equivalence. The basis is
unpriced. -/
noncomputable def h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    Module.Basis (Fin n) ℤ ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  (Pi.basisFun ℤ (Fin n)).map (G.latticeQuotEquiv B).symm

theorem latticeQuotEquiv_h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (i : Fin n) :
    G.latticeQuotEquiv B (G.h1Basis B i) = Pi.single i 1 := by
  rw [h1Basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply]

end IncidenceGraph

end Theaetetus
