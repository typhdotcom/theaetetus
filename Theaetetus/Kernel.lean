import Theaetetus.Pairing
import Descent.Geometry.Definiteness

/-! # The kernel interface: quadratic forms on finite prime sets

**The chamber vocabulary.** The
chamber theorems quantify over finite prime sets, so the
definiteness notions live on a kernel `K : ι → ι → ℝ` restricted
to a `Finset`: the quadratic form (`quadFormOn`), conditional
negative definiteness on zero-sum weights (`IsCNDOn`), positive
semidefiniteness (`IsPSDOn`). Symmetry and the zero diagonal are
properties of the pairing, not of the interface — the predicates
stay reusable for the saturation deficit and any future kernel.

On a finite set the kernel is a matrix (`kernelMatrix`), and
`IsCNDOn` is Descent's `CondNegSemidef` of that matrix
(`isCNDOn_iff_condNegSemidef`). The restriction lemmas
(`IsCNDOn.subset`, from Descent's `CondNegSemidef.submatrix`;
`IsPSDOn.subset`, weights extended by zero across `P ⊆ Q`) are the
monotonicity behind the chamber structure: enlarging the prime set
can only shrink the valid-scale set. -/

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

/-! ## Finite-set kernels as matrices -/

/-- The matrix of a kernel restricted to a finite index set. -/
def kernelMatrix (K : ι → ι → ℝ) (P : Finset ι) :
    Matrix P P ℝ :=
  Matrix.of fun i j => K i j

theorem quadFormOn_eq_dotProduct (K : ι → ι → ℝ)
    (P : Finset ι) (c : ι → ℝ) :
    quadFormOn K P c
      = dotProduct (fun i : P => c i)
          ((kernelMatrix K P).mulVec fun i : P => c i) := by
  unfold quadFormOn
  simp only [dotProduct, Matrix.mulVec, kernelMatrix, Matrix.of_apply,
    Finset.mul_sum]
  rw [← Finset.sum_coe_sort P]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort P]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Finite-set CND is matrix CND**: conditional negative
definiteness of a kernel on a finite set is conditional negative
semidefiniteness of its restricted matrix. -/
theorem isCNDOn_iff_condNegSemidef (K : ι → ι → ℝ)
    (P : Finset ι) :
    IsCNDOn K P ↔ Descent.CondNegSemidef (kernelMatrix K P) := by
  classical
  constructor
  · intro h x hx
    let c : ι → ℝ := fun p => if hp : p ∈ P then x ⟨p, hp⟩ else 0
    have hcx : (fun i : P => c i) = x := funext fun i => by simp [c]
    have hc : (∑ p ∈ P, c p) = 0 := by
      rw [← Finset.sum_coe_sort P, ← hx]
      exact Finset.sum_congr rfl fun i _ => congrFun hcx i
    have hq := h c hc
    rwa [quadFormOn_eq_dotProduct, hcx] at hq
  · intro h c hc
    rw [quadFormOn_eq_dotProduct]
    refine h _ ?_
    rw [Finset.sum_coe_sort P c]
    exact hc

/-- **Restriction, CND**: conditional negative definiteness on a
set restricts to every subset — the zero-sum weight extends by
zero. Thresholds are therefore monotone in the prime set. -/
theorem IsCNDOn.subset [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsCNDOn K Q) (hPQ : P ⊆ Q) :
    IsCNDOn K P := by
  rw [isCNDOn_iff_condNegSemidef] at hQ ⊢
  exact hQ.submatrix fun i : P => (⟨i, hPQ i.2⟩ : Q)

/-- **Restriction, PSD**: positive semidefiniteness on a set
restricts to every subset. -/
theorem IsPSDOn.subset [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsPSDOn K Q) (hPQ : P ⊆ Q) :
    IsPSDOn K P := by
  intro c
  have h := hQ (fun p => if p ∈ P then c p else 0)
  rwa [quadFormOn_extend K hPQ c] at h

/-- **The exact zero-sum identity**: on a set of
primes, against a zero-sum weight, the pairing's quadratic form is
the product-kernel's (Hankel-extension) quadratic form minus the
diagonal of midpoint curvatures — the `M = M̃ − diag(d)`
decomposition as an exact identity. On the diagonal the extension uses
`p²`, not `lcm(p,p) = p`. The base term `log θ(s)` and both
row/column terms cancel exactly against the zero-sum constraint;
no approximation enters. -/
theorem quadFormOn_pairing_eq {s : ℝ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) {c : ℕ → ℝ}
    (hc : (∑ p ∈ P, c p) = 0) :
    quadFormOn (pairing s) P c
      = (∑ p ∈ P, ∑ q ∈ P, c p * c q
          * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)))
        - ∑ p ∈ P, c p ^ 2
          * (Real.log (theta s)
            + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
            - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) := by
  -- the pointwise split: off the diagonal the pairing is the
  -- four-term coprime expansion; on it, both sides vanish
  have step1 : ∀ p ∈ P, ∀ q ∈ P,
      c p * c q * pairing s p q
        = c p * c q * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
          + c p * (c q * Real.log (theta s))
          - c p * Real.log (theta ((p : ℝ) ^ 2 * s)) * c q
          - c p * (c q * Real.log (theta ((q : ℝ) ^ 2 * s)))
          - (if q = p then c p ^ 2
              * (Real.log (theta s)
                + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
                - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) else 0) := by
    intro p hp q hq
    by_cases hqp : q = p
    · subst hqp
      rw [pairing_self, ite_eq_left rfl]
      ring
    · have hco : Nat.Coprime p q :=
        (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr (Ne.symm hqp)
      rw [ite_eq_right hqp]
      unfold pairing
      rw [defect_coprime hco]
      ring
  unfold quadFormOn
  rw [Finset.sum_congr rfl
    (fun p hp => Finset.sum_congr rfl fun q hq => step1 p hp q hq)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the base term dies row-by-row against the zero sum
  have hB : ∀ p ∈ P,
      (∑ q ∈ P, c p * (c q * Real.log (theta s))) = 0 := by
    intro p _
    rw [← Finset.mul_sum, ← Finset.sum_mul, hc, zero_mul, mul_zero]
  -- the p-row term dies row-by-row
  have hC : ∀ p ∈ P,
      (∑ q ∈ P, c p * Real.log (theta ((p : ℝ) ^ 2 * s)) * c q) = 0 := by
    intro p _
    rw [← Finset.mul_sum, hc, mul_zero]
  -- the q-column term dies at the outer level
  have hD : (∑ p ∈ P, ∑ q ∈ P,
      c p * (c q * Real.log (theta ((q : ℝ) ^ 2 * s)))) = 0 := by
    have hrow : ∀ p ∈ P,
        (∑ q ∈ P, c p * (c q * Real.log (theta ((q : ℝ) ^ 2 * s))))
          = c p * ∑ q ∈ P, c q * Real.log (theta ((q : ℝ) ^ 2 * s)) := by
      intro p _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, hc, zero_mul]
  -- the diagonal collapses to a single sum
  have hE : ∀ p ∈ P,
      (∑ q ∈ P, if q = p then c p ^ 2
          * (Real.log (theta s)
            + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
            - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) else 0)
        = c p ^ 2
          * (Real.log (theta s)
            + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
            - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) := by
    intro p hp
    rw [Finset.sum_ite_eq' P p, ite_eq_left hp]
  rw [Finset.sum_congr rfl hB, Finset.sum_congr rfl hC,
    Finset.sum_congr rfl hE, hD, Finset.sum_const_zero]
  ring

end Theaetetus
