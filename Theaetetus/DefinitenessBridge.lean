import Theaetetus.ResolutionMetric
import Theaetetus.Flattening
import Theaetetus.SmallScale
import Descent.Geometry.Definiteness

/-! # The definiteness bridge: the pairing as a sampled defect matrix

The kernel chambers are stated for the prime pairing restricted to a
finite set (`IsCNDOn`). The same object is Descent's sampled defect
datum: on a finite set of positive resolutions the pairing matrix is
the defect matrix of the normalized resolution field `−log θ(q²s)`
sampled there (`pairingMatrix_eq_defectMatrix`), and conditional
negative definiteness on a finite set is Descent's conditional
negative semidefiniteness of the restricted matrix
(`isCNDOn_iff_condNegSemidef`). The chamber theorems then read in
Descent's vocabulary (`condNegSemidef_resField_large`,
`not_condNegSemidef_resField_small`).

The bridge also explains why the chambers sample primes only. A
sample with a least element — here the base resolution `1` — has
vanishing defect against that element, so its centred Gram kernel
at the base is minus half the defect matrix; conditional negativity
then forces the matrix to be negative semidefinite, and a hollow
symmetric matrix is that only when it vanishes
(`condNegSemidef_defectMatrix_iff_of_base`). At rank one the defect
detects divisibility, so a positive sample containing `1` is CND at
a positive scale exactly when it is a divisibility chain
(`isCNDOn_pairing_iff_chain_of_one_mem`); `1` together with two
distinct primes is never CND (`not_isCNDOn_pairing_one_prime_prime`). -/

namespace Theaetetus

open Filter Topology

/-! ## Finite-set kernels as matrices -/

/-- The matrix of a kernel restricted to a finite index set. -/
def kernelMatrix {ι : Type*} (K : ι → ι → ℝ) (P : Finset ι) :
    Matrix P P ℝ :=
  Matrix.of fun i j => K i j

theorem quadFormOn_eq_dotProduct {ι : Type*} (K : ι → ι → ℝ)
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
theorem isCNDOn_iff_condNegSemidef {ι : Type*} (K : ι → ι → ℝ)
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

/-! ## Samples with a base point -/

/-- **Conditional negativity at a based sample**: when the sample
has a least element, the defect matrix is conditionally negative
semidefinite only if it vanishes. The defect against the base is
zero, so the centred Gram kernel at the base is minus half the
defect matrix, and a hollow matrix with positive semidefinite
negative is zero. -/
theorem condNegSemidef_defectMatrix_iff_of_base {R : Type*} [Lattice R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Descent.ContextField R ℝ}
    {r : ι → R} {i₀ : ι} (hbase : ∀ i, r i₀ ≤ r i) :
    Descent.CondNegSemidef (Descent.defectMatrix K r)
      ↔ Descent.defectMatrix K r = 0 := by
  have hgram : Descent.centeredGram (Descent.defectMatrix K r) i₀
      = (1 / 2 : ℝ) • -Descent.defectMatrix K r := by
    ext i j
    simp only [Descent.centeredGram_apply, Descent.defectMatrix_apply,
      Descent.defect_of_ge K (hbase i), Descent.defect_of_le K (hbase j),
      Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    ring
  rw [Descent.condNegSemidef_iff_posSemidef_centeredGram
    (Descent.isHermitian_defectMatrix K r) (Descent.defectMatrix_diag K r i₀),
    hgram, ← Descent.posSemidef_neg_defectMatrix_iff]
  constructor
  · intro h
    have h2 := h.smul (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at h2
  · intro h
    exact h.smul (by norm_num)

/-! ## The pairing as the defect matrix of the resolution field -/

/-- The resolution sample of a finite set of naturals: each
resolution read as a context of the divisibility carrier. -/
def resSample (P : Finset ℕ) : P → Descent.Arith :=
  fun p => Descent.Arith.of (Nat.toPNat' p)

theorem pairing_eq_defect_resField (s : ℝ) {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) :
    pairing s p q
      = Descent.defect (resField theta s) (Descent.Arith.of (Nat.toPNat' p))
          (Descent.Arith.of (Nat.toPNat' q)) := by
  rw [defect_resField, PNat.toPNat'_coe hp, PNat.toPNat'_coe hq, pairing,
    defect_eq_fieldDefect]

/-- **The pairing matrix is a defect matrix**: on a finite set of
positive resolutions the prime pairing is Descent's defect matrix of
the normalized resolution field, sampled at those resolutions. -/
theorem pairingMatrix_eq_defectMatrix (s : ℝ) {P : Finset ℕ}
    (hpos : ∀ p ∈ P, 0 < p) :
    kernelMatrix (pairing s) P
      = Descent.defectMatrix (resField theta s) (resSample P) := by
  ext i j
  exact pairing_eq_defect_resField s (hpos i i.2) (hpos j j.2)

/-- **CND of the pairing is CND of the sampled defect matrix.** -/
theorem isCNDOn_pairing_iff (s : ℝ) {P : Finset ℕ}
    (hpos : ∀ p ∈ P, 0 < p) :
    IsCNDOn (pairing s) P
      ↔ Descent.CondNegSemidef
          (Descent.defectMatrix (resField theta s) (resSample P)) := by
  rw [isCNDOn_iff_condNegSemidef, pairingMatrix_eq_defectMatrix s hpos]

/-! ## The chambers in Descent's vocabulary -/

/-- **The large-scale chamber, sampled**: for `s ≥ 1` the defect
matrix of the resolution field on every finite prime sample is
conditionally negative semidefinite. -/
theorem condNegSemidef_resField_large {s : ℝ} (hs : 1 ≤ s) {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    Descent.CondNegSemidef
      (Descent.defectMatrix (resField theta s) (resSample P)) :=
  (isCNDOn_pairing_iff s fun p hp => (hprime p hp).pos).mp
    (pairing_cnd_large hs hprime)

/-- **The small-scale chamber, sampled**: on a prime sample of at
least three primes the sampled defect matrix fails conditional
negativity at all small scales. -/
theorem not_condNegSemidef_resField_small (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hcard : 3 ≤ P.card) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ¬ Descent.CondNegSemidef
          (Descent.defectMatrix (resField theta s) (resSample P)) := by
  obtain ⟨ε, hε, h⟩ := pairing_not_cnd_small P hprime hcard
  exact ⟨ε, hε, fun s hs hsε hc =>
    h s hs hsε ((isCNDOn_pairing_iff s fun p hp => (hprime p hp).pos).mpr hc)⟩

/-! ## The base resolution forbids conditional negativity -/

/-- **With the base, CND is a chain condition**: at a positive scale,
the pairing on a finite set of positive resolutions containing `1`
is CND exactly when the set is a divisibility chain. -/
theorem isCNDOn_pairing_iff_chain_of_one_mem {s : ℝ} (hs : 0 < s)
    {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p) (h1 : 1 ∈ P) :
    IsCNDOn (pairing s) P ↔ ∀ p ∈ P, ∀ q ∈ P, p ∣ q ∨ q ∣ p := by
  rw [isCNDOn_pairing_iff s hpos,
    condNegSemidef_defectMatrix_iff_of_base (i₀ := ⟨1, h1⟩)
      fun i => Descent.Arith.le_iff_dvd.mpr (by
        show ((Nat.toPNat' 1 : ℕ+) : ℕ) ∣ _
        exact one_dvd _),
    ← pairingMatrix_eq_defectMatrix s hpos]
  constructor
  · intro h p hp q hq
    have he := congrFun (congrFun h ⟨p, hp⟩) ⟨q, hq⟩
    simp only [kernelMatrix, Matrix.of_apply, Matrix.zero_apply, pairing,
      neg_eq_zero] at he
    exact (defect_eq_zero_iff hs).mp he
  · intro h
    ext i j
    simp only [kernelMatrix, Matrix.of_apply, Matrix.zero_apply, pairing,
      neg_eq_zero]
    exact (defect_eq_zero_iff hs).mpr (h i i.2 j j.2)

/-- **The base and two primes are never CND**: at every positive
scale, a finite set of positive resolutions containing `1` and two
distinct primes carries a pairing that is not conditionally negative
definite — the sampled defect matrix fails `CondNegSemidef`. -/
theorem not_isCNDOn_pairing_one_prime_prime {s : ℝ} (hs : 0 < s)
    {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p) (h1 : 1 ∈ P) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpP : p ∈ P)
    (hqP : q ∈ P) :
    ¬ IsCNDOn (pairing s) P := by
  rw [isCNDOn_pairing_iff_chain_of_one_mem hs hpos h1]
  intro h
  have hne := (pairing_pos hs hp hq hpq).ne'
  rw [pairing, neg_ne_zero, Ne, defect_eq_zero_iff hs] at hne
  exact hne (h p hpP q hqP)

end Theaetetus
