import Theaetetus.Pairing

/-! # The kernel interface: quadratic forms on finite prime sets

**Q4's vocabulary** (README: Q4 and the ladder, rungs 5–6). The
chamber theorems quantify over finite prime sets, so the
definiteness notions live on a kernel `K : ι → ι → ℝ` restricted
to a `Finset`: the quadratic form (`quadFormOn`), conditional
negative definiteness on zero-sum weights (`IsCNDOn`), positive
semidefiniteness (`IsPSDOn`). Symmetry and the zero diagonal are
properties of the pairing, not of the interface — the predicates
stay reusable for the saturation deficit and any future kernel.

The restriction lemmas (`IsCNDOn.subset`, `IsPSDOn.subset`) —
weights extend by zero across `P ⊆ Q` — are the monotonicity
behind the chamber structure: enlarging the prime set can only
shrink the valid-scale set. -/

namespace Theaetetus

variable {ι : Type*}

/-- The quadratic form of a kernel `K` on a finite index set `P`
with weights `c`. -/
def quadFormOn (K : ι → ι → ℝ) (P : Finset ι) (c : ι → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, c p * c q * K p q

/-- **Conditional negative definiteness** on a finite set: every
zero-sum weight has nonpositive energy. -/
def IsCNDOn (K : ι → ι → ℝ) (P : Finset ι) : Prop :=
  ∀ c : ι → ℝ, (∑ p ∈ P, c p) = 0 → quadFormOn K P c ≤ 0

/-- **Positive semidefiniteness** on a finite set. -/
def IsPSDOn (K : ι → ι → ℝ) (P : Finset ι) : Prop :=
  ∀ c : ι → ℝ, 0 ≤ quadFormOn K P c

/-- Extending a weight by zero from `P ⊆ Q` leaves the quadratic
form unchanged: the added rows and columns carry weight zero. -/
theorem quadFormOn_extend [DecidableEq ι] (K : ι → ι → ℝ)
    {P Q : Finset ι} (hPQ : P ⊆ Q) (c : ι → ℝ) :
    quadFormOn K Q (fun p => if p ∈ P then c p else 0)
      = quadFormOn K P c := by
  unfold quadFormOn
  rw [← Finset.sum_subset hPQ
    (fun p _ hp => Finset.sum_eq_zero fun q _ => by simp [hp])]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_subset
    (f := fun q =>
      (if p ∈ P then c p else 0) * (if q ∈ P then c q else 0) * K p q)
    hPQ (fun q _ hq => by simp [hq])]
  exact Finset.sum_congr rfl fun q hq => by simp [hp, hq]

/-- **Restriction, CND**: conditional negative definiteness on a
set restricts to every subset — the zero-sum weight extends by
zero. Thresholds are therefore monotone in the prime set. -/
theorem IsCNDOn.subset [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsCNDOn K Q) (hPQ : P ⊆ Q) :
    IsCNDOn K P := by
  intro c hc
  have hzero : (∑ p ∈ Q, if p ∈ P then c p else 0) = 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hPQ]
    exact hc
  have h := hQ (fun p => if p ∈ P then c p else 0) hzero
  rwa [quadFormOn_extend K hPQ c] at h

/-- **Restriction, PSD**: positive semidefiniteness on a set
restricts to every subset. -/
theorem IsPSDOn.subset [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsPSDOn K Q) (hPQ : P ⊆ Q) :
    IsPSDOn K P := by
  intro c
  have h := hQ (fun p => if p ∈ P then c p else 0)
  rwa [quadFormOn_extend K hPQ c] at h

end Theaetetus
