import Theaetetus.FiniteIndex
import Descent.Core.Defect
import Descent.Core.Higher

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

The capstone follows in one rewrite. The exact order-three
recurrence writes `D₃` as three pairwise defects plus the field gap
across the distributivity-defect interval; at the boundary every
pairwise term vanishes and the gap becomes the logarithm of the
interval's index, so

    D₃,s(A,B,C) → log [ (A+B)∩C : (A∩C)+(B∩C) ]   as s → 0⁺

(`tendsto_defect3_subField`, over `distribUpper`, `distribLower`,
`distribLower_le_upper`). That is the whole reading: the Gaussian
field becomes pairwise modular at the boundary, but
non-distributivity leaves a finite interval, and the entire
surviving third-order interaction is the logarithm of that
interval's index.

Finite index is the only hypothesis the public statements carry;
every meet and join the recurrence uses inherits it, and the charts
are internal (`subBasis`). The chart-level theorems remain as
implementation API. -/

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
theorem tendsto_defect_subField_chart {A B : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hB : B.index ≠ 0)
    (bA : Module.Basis (Fin d) ℤ A) (bB : Module.Basis (Fin d) ℤ B)
    (bI : Module.Basis (Fin d) ℤ (A ⊓ B : AddSubgroup (Fin d → ℤ)))
    (bS : Module.Basis (Fin d) ℤ (A ⊔ B : AddSubgroup (Fin d → ℤ))) :
    Tendsto (fun s => Descent.defect (subField s) A B) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
  have hI : (A ⊓ B).index ≠ 0 := AddSubgroup.index_inf_ne_zero hA hB
  have hS : (A ⊔ B).index ≠ 0 := index_sup_ne_zero hA
  have h1 := tendsto_log_subMass_sub_chart (le_sup_left : A ≤ A ⊔ B) hS hA
    bS bA
  have h2 := tendsto_log_subMass_sub_chart (inf_le_right : A ⊓ B ≤ B) hB hI
    bB bI
  have hiso : (A ⊓ B).relIndex B = A.relIndex (A ⊔ B) := by
    rw [AddSubgroup.inf_relIndex_right, sup_comm,
      AddSubgroup.relIndex_sup_right]
  have hsub := h2.sub h1
  rw [hiso, sub_self] at hsub
  refine hsub.congr fun s => ?_
  rw [Descent.defect_def]
  simp only [subField_apply]
  ring

/-- **The pairwise boundary theorem**, chart-free: only the two
nonzero-index hypotheses are needed. -/
theorem tendsto_defect_subField {A B : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hB : B.index ≠ 0) :
    Tendsto (fun s => Descent.defect (subField s) A B) (𝓝[>] (0 : ℝ))
      (𝓝 0) :=
  tendsto_defect_subField_chart hA hB (subBasis hA) (subBasis hB)
    (subBasis (AddSubgroup.index_inf_ne_zero hA hB))
    (subBasis (index_sup_ne_zero hA))

/-! ## The distributivity-defect interval -/

/-- The upper end of the distributivity-defect interval of a
comparison triple: the meet of the join. -/
def distribUpper (A B C : AddSubgroup (Fin d → ℤ)) :
    AddSubgroup (Fin d → ℤ) :=
  (A ⊔ B) ⊓ C

/-- The lower end: the join of the meets. -/
def distribLower (A B C : AddSubgroup (Fin d → ℤ)) :
    AddSubgroup (Fin d → ℤ) :=
  (A ⊓ C) ⊔ (B ⊓ C)

/-- The interval is an interval: distributivity holds one way
round. -/
theorem distribLower_le_upper (A B C : AddSubgroup (Fin d → ℤ)) :
    distribLower A B C ≤ distribUpper A B C :=
  sup_le (inf_le_inf_right C le_sup_left) (inf_le_inf_right C le_sup_right)

theorem index_distribUpper_ne_zero {A B C : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hC : C.index ≠ 0) :
    (distribUpper A B C).index ≠ 0 :=
  AddSubgroup.index_inf_ne_zero (index_sup_ne_zero hA) hC

theorem index_distribLower_ne_zero {A B C : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hC : C.index ≠ 0) :
    (distribLower A B C).index ≠ 0 :=
  index_sup_ne_zero (AddSubgroup.index_inf_ne_zero hA hC)

/-! ## The third-order boundary value -/

/-- **The distributivity-index law for a comparison triple of
finite-index subgroups**: at the boundary the pairwise defects all
vanish, and the entire surviving third-order interaction is the
logarithm of the index of the distributivity-defect interval. -/
theorem tendsto_defect3_subField {A B C : AddSubgroup (Fin d → ℤ)}
    (hA : A.index ≠ 0) (hB : B.index ≠ 0) (hC : C.index ≠ 0) :
    Tendsto (fun s => Descent.defect3 (subField s) A B C) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((((distribLower A B C).relIndex
        (distribUpper A B C) : ℕ)) : ℝ))) := by
  have hpair1 := tendsto_defect_subField hA hB
  have hpair2 := tendsto_defect_subField
    (index_sup_ne_zero (B := B) hA) hC
  have hpair3 := tendsto_defect_subField
    (AddSubgroup.index_inf_ne_zero hA hC)
    (AddSubgroup.index_inf_ne_zero hB hC)
  have hgap := tendsto_log_subMass_sub (distribLower_le_upper A B C)
    (index_distribUpper_ne_zero hA hC) (index_distribLower_ne_zero hA hC)
  have hsum := ((hpair1.add hpair2).sub hpair3).add hgap
  norm_num at hsum
  exact hsum.congr fun s => (Descent.defect3_recurrence _ _ _ _).symm

end Theaetetus
