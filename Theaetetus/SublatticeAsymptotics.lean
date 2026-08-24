import Theaetetus.FiniteIndex
import Descent.Core.Defect

/-! # The pairwise boundary of the sublattice field

The Gaussian mass of a subgroup, read logarithmically, is a context
field on the subgroups of the integer lattice (`subField`). At the
small-scale boundary that field becomes modular.

The reason is covolume. Along a full-rank finite-index inclusion the
two log-masses differ, in the limit, by the logarithm of the index
(`tendsto_log_subMass_sub`). Applied to `A ≤ A + B` and to
`A ∩ B ≤ B` this leaves the two indices `[A+B : A]` and `[B : A∩B]`,
which the second isomorphism theorem equates
(`AddSubgroup.relIndex_sup_right`). The pairwise defect is exactly
the difference of those two logarithms, so it vanishes
(`tendsto_defect_subField`): covolume is multiplicative across meet
and join, and the boundary field loses its pairwise curvature.

That is what leaves room for an order-three value. With every
pairwise term gone at the boundary, whatever survives the
order-three recurrence can only be the field gap across the
distributivity-defect interval — the index of that interval. The
composition is not performed here.

Full rank and finite index are carried explicitly: the index
hypotheses on the two subgroups, and a chart witness for each of the
four subgroups involved. -/

namespace Theaetetus

open Filter Topology

variable {d : ℕ}

/-- The fixed-scale logarithmic field on the subgroups of the
integer lattice: each subgroup priced by the logarithm of its
Gaussian mass. -/
noncomputable def subField (s : ℝ) :
    Descent.ContextField (AddSubgroup (Fin d → ℤ)) ℝ :=
  fun H => Real.log (subMass s H)

theorem subField_apply (s : ℝ) (H : AddSubgroup (Fin d → ℤ)) :
    subField s H = Real.log (subMass s H) :=
  rfl

/-- The sum of two finite-index subgroups has finite index. -/
theorem index_sup_ne_zero {A B : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) : (A ⊔ B).index ≠ 0 := by
  intro h
  exact hA (Nat.eq_zero_of_zero_dvd
    (h ▸ AddSubgroup.index_dvd_of_le le_sup_left))

/-- **The pairwise boundary theorem**: at the small-scale boundary
the logarithmic Gaussian field of full-rank finite-index subgroups
becomes modular — its pairwise defect vanishes. Covolume is
multiplicative across meet and join, so the two index limits cancel
by the second isomorphism theorem, and the field loses its pairwise
curvature. -/
theorem tendsto_defect_subField {A B : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hB : B.index ≠ 0)
    (bA : Module.Basis (Fin d) ℤ A) (bB : Module.Basis (Fin d) ℤ B)
    (bI : Module.Basis (Fin d) ℤ (A ⊓ B : AddSubgroup (Fin d → ℤ)))
    (bS : Module.Basis (Fin d) ℤ (A ⊔ B : AddSubgroup (Fin d → ℤ))) :
    Tendsto (fun s => Descent.defect (subField s) A B) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
  have hI : (A ⊓ B).index ≠ 0 := AddSubgroup.index_inf_ne_zero hA hB
  have hS : (A ⊔ B).index ≠ 0 := index_sup_ne_zero hA
  have h1 := tendsto_log_subMass_sub (le_sup_left : A ≤ A ⊔ B) hS hA bS bA
  have h2 := tendsto_log_subMass_sub (inf_le_right : A ⊓ B ≤ B) hB hI bB bI
  have hiso : (A ⊓ B).relIndex B = A.relIndex (A ⊔ B) := by
    rw [AddSubgroup.inf_relIndex_right, sup_comm,
      AddSubgroup.relIndex_sup_right]
  have hsub := h2.sub h1
  rw [hiso, sub_self] at hsub
  refine hsub.congr fun s => ?_
  rw [Descent.defect_def]
  simp only [subField_apply]
  ring

end Theaetetus
