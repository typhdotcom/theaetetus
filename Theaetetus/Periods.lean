import Theaetetus.GramData
import Theaetetus.GraphHomology
import Theaetetus.Periodization

/-! # Period-Model Harmonic Data: the General Finite-Graph API

The least-norm-at-prescribed-periods lemma,
packaged as a **builder**: any family of
cycle vectors
with positive-definite chain Gram matrix yields a `HarmonicGramData`
whose Gram form is the *inverse* chain Gram — with the variational
identity as a theorem, not an assertion.

The cycle graph `C_n` enters through the single all-ones basis cycle
(`cycleAllOnes`) with chain Gram `[[n]]` (`gramOf_cycleAllOnes`). -/

namespace Theaetetus

open scoped BigOperators
open Matrix

/-! ## Least norm at prescribed periods -/

section PeriodMinimization

variable {ι : Type*} [Fintype ι] {r : ℕ}

/-- Gram matrix of a family of period vectors under the standard
(unit-edge) dot product — the canonical pricing datum, *derived* from
the family, never stored. It lives here, in the
variational layer, not in the topology layer:
the Gram **is** pricing. -/
noncomputable def gramOf (c : Fin r → ι → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => c i ⬝ᵥ c j

theorem gramOf_isSymm (c : Fin r → ι → ℝ) : (gramOf c).IsSymm := by
  ext i j
  exact dotProduct_comm (c j) (c i)

/-- The quadratic form of a Gram matrix is the squared norm of the
combination: `xᵀ(gramOf c)x = ‖Σᵢ xᵢcᵢ‖²`. -/
theorem dotProduct_gramOf_mulVec {r : ℕ} {ι : Type*} [Fintype ι]
    (c : Fin r → ι → ℝ) (x : Fin r → ℝ) :
    x ⬝ᵥ (gramOf c *ᵥ x)
      = (fun e => ∑ i, x i * c i e) ⬝ᵥ (fun e => ∑ i, x i * c i e) := by
  show ∑ i, x i * (∑ j, gramOf c i j * x j)
    = ∑ e, (∑ i, x i * c i e) * (∑ j, x j * c j e)
  calc ∑ i, x i * (∑ j, gramOf c i j * x j)
      = ∑ i, ∑ j, x i * x j * (∑ e, c i e * c j e) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        show x i * (gramOf c i j * x j) = x i * x j * (∑ e, c i e * c j e)
        rw [show gramOf c i j = ∑ e, c i e * c j e from rfl]
        ring
    _ = ∑ i, ∑ j, ∑ e, x i * x j * (c i e * c j e) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ e, ∑ j, x i * x j * (c i e * c j e) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ e, ∑ i, ∑ j, x i * x j * (c i e * c j e) := Finset.sum_comm
    _ = ∑ e, (∑ i, x i * c i e) * (∑ j, x j * c j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring

/-- The minimum-norm cochain with periods `k`: the combination of the
period vectors with coefficients `C⁻¹k`. -/
noncomputable def periodRep (c : Fin r → ι → ℝ) (k : Fin r → ℝ) : ι → ℝ :=
  fun e => ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e

/-- A dot product against a member of the family, for any coefficient
combination: `⟨∑ᵢ xᵢcᵢ, cⱼ⟩ = (x ᵥ* C) j`. -/
private lemma comb_dotProduct (c : Fin r → ι → ℝ) (x : Fin r → ℝ) (j : Fin r) :
    (fun e => ∑ i, x i * c i e) ⬝ᵥ c j = ∑ i, x i * gramOf c i j := by
  calc (fun e => ∑ i, x i * c i e) ⬝ᵥ c j
      = ∑ e, (∑ i, x i * c i e) * c j e := rfl
    _ = ∑ e, ∑ i, x i * c i e * c j e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ e, x i * c i e * c j e := Finset.sum_comm
    _ = ∑ i, x i * gramOf c i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        show _ = x i * ∑ e, c i e * c j e
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- The minimum-norm cochain has the prescribed periods. -/
theorem periodRep_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) (j : Fin r) :
    periodRep c k ⬝ᵥ c j = k j := by
  rw [show periodRep c k = fun e => ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e from rfl,
    comb_dotProduct]
  have hCT : (gramOf c)ᵀ = gramOf c := gramOf_isSymm c
  have hv : (((gramOf c)⁻¹.mulVec k) ᵥ* gramOf c) j = k j := by
    calc (((gramOf c)⁻¹.mulVec k) ᵥ* gramOf c) j
        = (((gramOf c)⁻¹.mulVec k) ᵥ* ((gramOf c)ᵀ)ᵀ) j := by
          rw [Matrix.transpose_transpose]
      _ = ((gramOf c)ᵀ *ᵥ ((gramOf c)⁻¹ *ᵥ k)) j := by
          rw [Matrix.vecMul_transpose]
      _ = (gramOf c *ᵥ ((gramOf c)⁻¹ *ᵥ k)) j := by rw [hCT]
      _ = k j := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC,
            Matrix.one_mulVec]
  exact hv

/-- Energy of the minimum-norm cochain: `kᵀC⁻¹k`. -/
theorem periodRep_energy (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) :
    periodRep c k ⬝ᵥ periodRep c k = k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) := by
  have h1 : periodRep c k ⬝ᵥ periodRep c k
      = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i) := by
    calc periodRep c k ⬝ᵥ periodRep c k
        = ∑ e, periodRep c k e * ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e := rfl
      _ = ∑ e, ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k e * c i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k e * c i e) :=
          Finset.sum_comm
      _ = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          rfl
  rw [h1]
  calc ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i)
      = ∑ i, ((gramOf c)⁻¹.mulVec k) i * k i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [periodRep_periods c hC k i]
    _ = ((gramOf c)⁻¹.mulVec k) ⬝ᵥ k := rfl
    _ = k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) := dotProduct_comm _ _

/-- **Pythagoras**: any cochain with the prescribed periods has energy
at least `kᵀC⁻¹k`. -/
theorem le_energy_of_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) (ω : ι → ℝ) (hω : ∀ j, ω ⬝ᵥ c j = k j) :
    k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) ≤ ω ⬝ᵥ ω := by
  set δ : ι → ℝ := ω - periodRep c k with hδ
  have hδc : ∀ j, δ ⬝ᵥ c j = 0 := fun j => by
    rw [hδ, sub_dotProduct, hω j, periodRep_periods c hC k j, sub_self]
  have hcross : periodRep c k ⬝ᵥ δ = 0 := by
    calc periodRep c k ⬝ᵥ δ
        = ∑ e, (∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e) * δ e := rfl
      _ = ∑ e, ∑ i, ((gramOf c)⁻¹.mulVec k) i * (c i e * δ e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, ((gramOf c)⁻¹.mulVec k) i * (c i e * δ e) :=
          Finset.sum_comm
      _ = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (δ ⬝ᵥ c i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hδc i, mul_zero]
  have hω_eq : ω = periodRep c k + δ := by
    funext e
    simp [hδ]
  have hexpand : ω ⬝ᵥ ω
      = periodRep c k ⬝ᵥ periodRep c k + 2 * (periodRep c k ⬝ᵥ δ) + δ ⬝ᵥ δ := by
    rw [hω_eq, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm δ (periodRep c k)]
    ring
  have hδδ : 0 ≤ δ ⬝ᵥ δ :=
    Finset.sum_nonneg fun e _ => mul_self_nonneg (δ e)
  rw [hexpand, hcross, periodRep_energy c hC k]
  linarith

/-- **The variational identity, packaged**: `kᵀC⁻¹k` is the least
energy among cochains with periods `k` — attained, with witness
`periodRep`. This is the Hodge variational principle in its
cohomological (period) formulation. -/
theorem isLeast_energy_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) :
    IsLeast {E : ℝ | ∃ ω : ι → ℝ, (∀ j, ω ⬝ᵥ c j = k j) ∧ E = ω ⬝ᵥ ω}
      (k ⬝ᵥ ((gramOf c)⁻¹.mulVec k)) :=
  ⟨⟨periodRep c k, fun j => periodRep_periods c hC k j,
      (periodRep_energy c hC k).symm⟩,
    fun _ ⟨ω, hω, hE⟩ => hE ▸ le_energy_of_periods c hC k ω hω⟩

end PeriodMinimization

/-! ## The priced Gram of a lattice basis -/

section LatticeBasisGram

universe u'

variable (G : IncidenceGraph.{u'}) {n : ℕ}
  (B : Module.Basis (Fin n) ℤ G.cycleLattice)

/-- **The unit-edge Gram of a lattice basis is positive definite** —
derived, with nothing stored, and located in
the priced layer where the Gram lives: the
quadratic form is the squared norm of the combination, which vanishes
only at zero by independence (`cast_independent`, topology layer). -/
theorem IncidenceGraph.gramOf_cyclesR_posDef :
    (gramOf (G.cyclesR B)).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext p q'
    show star (gramOf (G.cyclesR B) q' p) = gramOf (G.cyclesR B) p q'
    rw [star_trivial]
    show ∑ e, G.cyclesR B q' e * G.cyclesR B p e
      = ∑ e, G.cyclesR B p e * G.cyclesR B q' e
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · have hsx : star x = x := funext fun i => star_trivial _
    rw [hsx, dotProduct_gramOf_mulVec]
    have hynn : (0 : ℝ) ≤ (fun e => ∑ i, x i * G.cyclesR B i e)
        ⬝ᵥ (fun e => ∑ i, x i * G.cyclesR B i e) :=
      Finset.sum_nonneg fun e _ => mul_self_nonneg _
    have hyne : (fun e => ∑ i, x i * G.cyclesR B i e) ≠ 0 :=
      fun h0 => hx (G.cast_independent B x h0)
    have hne : (fun e => ∑ i, x i * G.cyclesR B i e)
        ⬝ᵥ (fun e => ∑ i, x i * G.cyclesR B i e) ≠ 0 :=
      fun h0 => hyne (dotProduct_self_eq_zero.mp h0)
    exact lt_of_le_of_ne hynn (Ne.symm hne)

end LatticeBasisGram

/-! ## The builder: cycles to harmonic Gram data -/

section Builder

universe u

variable {V : Type u} {ι : Type*} [Fintype ι] {r : ℕ}

/-- **The builder**: cycle vectors with positive-definite chain Gram
yield harmonic Gram data with the inverse chain Gram as period form.
Symmetry, positive-definiteness, summability all derived. -/
noncomputable def HarmonicGramData.ofCycles (c : Fin r → ι → ℝ)
    (hC : (gramOf c).PosDef) : HarmonicGramData V where
  r := r
  gram := (gramOf c)⁻¹
  gram_posDef := posDef_inv hC

/-- The builder's data satisfies the variational identity: the Gram
energy of sector `k` is the least cochain energy at periods `k`. -/
theorem HarmonicGramData.ofCycles_energy_isLeast (c : Fin r → ι → ℝ)
    (hC : (gramOf c).PosDef) (k : Fin r → ℤ) :
    IsLeast {E : ℝ | ∃ ω : ι → ℝ,
        (∀ j, ω ⬝ᵥ c j = (k j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      ((HarmonicGramData.ofCycles (V := V) c hC).energy k) := by
  have hdet : IsUnit (gramOf c).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  have h := isLeast_energy_periods c hdet (fun j => (k j : ℝ))
  have hval : (HarmonicGramData.ofCycles (V := V) c hC).energy k
      = (fun j => (k j : ℝ)) ⬝ᵥ ((gramOf c)⁻¹.mulVec (fun j => (k j : ℝ))) := by
    show ∑ i, ∑ j, (gramOf c)⁻¹ i j * (k i : ℝ) * (k j : ℝ) = _
    rw [quadForm_dotProduct]
  rw [hval]
  exact h

end Builder

/-! ## The cycle graph `C_n` through periods

Edges `e : Fin n` run from vertex `e` to vertex `e + 1` (cyclically).
One basis cycle: the all-ones cochain, with chain Gram `[[n]]`. -/

section CyclePeriods

variable (n : ℕ)

/-- The single basis cycle: the all-ones cochain. -/
noncomputable def cycleAllOnes : Fin 1 → Fin n → ℝ := fun _ _ => 1

/-- The chain Gram of the cycle graph: `[[n]]`. -/
theorem gramOf_cycleAllOnes : gramOf (cycleAllOnes n) = !![(n : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  show (cycleAllOnes n 0) ⬝ᵥ (cycleAllOnes n 0) = (n : ℝ)
  simp [cycleAllOnes, dotProduct]

end CyclePeriods

end Theaetetus
