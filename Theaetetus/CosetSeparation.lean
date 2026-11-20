import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-! # Coset separation of Schiemann's quaternary pair

For an integral Gram matrix `G` on `ℤⁿ` and a level `m`, the
**class pairs** are the ordered pairs of distinct sectors of energy
`m` congruent modulo `2`: the second falling moment, at level `m`,
of the per-class sector counts of `ℤⁿ ⧸ 2ℤⁿ`. An integral isometry
carries class pairs bijectively onto class pairs
(`classPairs_ncard_eq_of_isometry`), so their count is an isometry
invariant.

Schiemann's Gram matrices `schiemannA` and `schiemannB` (determinant
`1729`) have ten sectors each at energy `12`
(`schiemannA_shell`, `schiemannB_shell`), but `10` and `18` class
pairs there (`schiemannA_classPairs_ncard`,
`schiemannB_classPairs_ncard`): the mod-`2` residue datum separates
them, and no integral isometry joins them
(`schiemann_not_isometric`). The shells are certified by
diagonal dominance, which confines energy `12` to the box
`[-3, 3]⁴`, and an exhaustive kernel check of that box. -/

namespace Theaetetus

open Matrix

variable {n : ℕ}

/-- The integral energy `xᵀ G x`. -/
def intEnergy (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  x ⬝ᵥ G *ᵥ x

/-- Ordered pairs of distinct sectors of energy `m`, congruent
modulo `2`. -/
def classPairs (G : Matrix (Fin n) (Fin n) ℤ) (m : ℤ) :
    Set ((Fin n → ℤ) × (Fin n → ℤ)) :=
  {p | intEnergy G p.1 = m ∧ intEnergy G p.2 = m ∧ p.1 ≠ p.2 ∧
    ∀ i, (2 : ℤ) ∣ p.1 i - p.2 i}

theorem intEnergy_mulVec (G U : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    intEnergy G (U *ᵥ x) = intEnergy (Uᵀ * G * U) x := by
  simp only [intEnergy, ← mulVec_mulVec, dotProduct_mulVec _ Uᵀ,
    vecMul_transpose]

theorem two_dvd_mulVec_sub (U : Matrix (Fin n) (Fin n) ℤ)
    {x y : Fin n → ℤ} (h : ∀ i, (2 : ℤ) ∣ x i - y i) (i : Fin n) :
    (2 : ℤ) ∣ (U *ᵥ x) i - (U *ᵥ y) i := by
  rw [← Pi.sub_apply, ← mulVec_sub]
  show (2 : ℤ) ∣ ∑ j, U i j * (x - y) j
  exact Finset.dvd_sum fun j _ => by simpa using (h j).mul_left (U i j)

/-- **Class pairs are an isometry invariant.** -/
theorem classPairs_ncard_eq_of_isometry (G : Matrix (Fin n) (Fin n) ℤ)
    (U : GL (Fin n) ℤ) (m : ℤ) :
    (classPairs ((U : Matrix (Fin n) (Fin n) ℤ)ᵀ * G *
      (U : Matrix (Fin n) (Fin n) ℤ)) m).ncard =
      (classPairs G m).ncard := by
  set V : Matrix (Fin n) (Fin n) ℤ := ↑U
  set W : Matrix (Fin n) (Fin n) ℤ := ↑(U⁻¹ : GL (Fin n) ℤ)
  have hWV : W * V = 1 := by simp [V, W]
  have hVW : V * W = 1 := by simp [V, W]
  have back : ∀ x : Fin n → ℤ, W *ᵥ (V *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, hWV, one_mulVec]
  have fwd : ∀ x : Fin n → ℤ, V *ᵥ (W *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, hVW, one_mulVec]
  refine Set.ncard_congr (fun p _ => (V *ᵥ p.1, V *ᵥ p.2)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ ⟨hx, hy, hne, hdvd⟩
    refine ⟨?_, ?_, ?_, two_dvd_mulVec_sub V hdvd⟩
    · simpa [intEnergy_mulVec] using hx
    · simpa [intEnergy_mulVec] using hy
    · intro h
      exact hne (by simpa [back] using congrArg (W *ᵥ ·) h)
  · rintro ⟨x, y⟩ ⟨x', y'⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    have h1 := congrArg (W *ᵥ ·) h.1
    have h2 := congrArg (W *ᵥ ·) h.2
    simp only [back] at h1 h2
    rw [h1, h2]
  · rintro ⟨a, b⟩ ⟨ha, hb, hne, hdvd⟩
    refine ⟨(W *ᵥ a, W *ᵥ b), ⟨?_, ?_, ?_, two_dvd_mulVec_sub W hdvd⟩, ?_⟩
    · rw [← intEnergy_mulVec, fwd]; exact ha
    · rw [← intEnergy_mulVec, fwd]; exact hb
    · intro h
      exact hne (by simpa [fwd] using congrArg (V *ᵥ ·) h)
    · simp [fwd]

/-- Schiemann's first Gram matrix. -/
def schiemannA : Matrix (Fin 4) (Fin 4) ℤ :=
  !![4, 2, 0, 1; 2, 8, 3, 1; 0, 3, 10, 5; 1, 1, 5, 10]

/-- Schiemann's second Gram matrix. -/
def schiemannB : Matrix (Fin 4) (Fin 4) ℤ :=
  !![4, 0, 1, 1; 0, 8, 1, -4; 1, 1, 8, 2; 1, -4, 2, 10]

theorem schiemannA_det : schiemannA.det = 1729 := by
  simp [schiemannA, det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem schiemannB_det : schiemannB.det = 1729 := by
  simp [schiemannB, det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The energy of `schiemannA` as a polynomial. -/
def energyA (a b c d : ℤ) : ℤ :=
  4 * a * a + 8 * b * b + 10 * c * c + 10 * d * d +
    2 * (2 * a * b + a * d + 3 * b * c + b * d + 5 * c * d)

/-- The energy of `schiemannB` as a polynomial. -/
def energyB (a b c d : ℤ) : ℤ :=
  4 * a * a + 8 * b * b + 8 * c * c + 10 * d * d +
    2 * (a * c + a * d + b * c - 4 * b * d + 2 * c * d)

theorem intEnergy_schiemannA (x : Fin 4 → ℤ) :
    intEnergy schiemannA x = energyA (x 0) (x 1) (x 2) (x 3) := by
  simp [intEnergy, schiemannA, energyA, dotProduct, mulVec, Fin.sum_univ_four]
  ring

theorem intEnergy_schiemannB (x : Fin 4 → ℤ) :
    intEnergy schiemannB x = energyB (x 0) (x 1) (x 2) (x 3) := by
  simp [intEnergy, schiemannB, energyB, dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- Diagonal dominance as a sum of squares: margin `1`. -/
theorem sum_sq_le_energyA (a b c d : ℤ) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ energyA a b c d := by
  unfold energyA
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + d), sq_nonneg (b + c),
    sq_nonneg (b + d), sq_nonneg (c + d), sq_nonneg a, sq_nonneg b,
    sq_nonneg c, sq_nonneg d]

/-- Diagonal dominance as a sum of squares: margin `2`. -/
theorem sum_sq_le_energyB (a b c d : ℤ) :
    2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ energyB a b c d := by
  unfold energyB
  nlinarith [sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c),
    sq_nonneg (b - d), sq_nonneg (c + d), sq_nonneg a, sq_nonneg b,
    sq_nonneg c, sq_nonneg d]

theorem abs_le_three_of_sq_le {a b c d : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 12) :
    a ∈ Finset.Icc (-3) 3 ∧ b ∈ Finset.Icc (-3) 3 ∧
      c ∈ Finset.Icc (-3) 3 ∧ d ∈ Finset.Icc (-3) 3 := by
  simp only [Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-- The sectors of `schiemannA` at energy `12`, as tuples. -/
def shellA : Finset (ℤ × ℤ × ℤ × ℤ) :=
  {(-1, 0, -1, 1), (-1, 0, 0, 1), (-1, 1, -1, 0), (-1, 1, -1, 1),
    (0, -1, 1, 0), (0, 1, -1, 0), (1, -1, 1, -1), (1, -1, 1, 0),
    (1, 0, 0, -1), (1, 0, 1, -1)}

/-- The sectors of `schiemannB` at energy `12`, as tuples. -/
def shellB : Finset (ℤ × ℤ × ℤ × ℤ) :=
  {(-1, -1, 0, 0), (-1, 0, 0, 1), (-1, 1, 0, 0), (-1, 1, 0, 1),
    (0, -1, 1, -1), (0, 1, -1, 1), (1, -1, 0, -1), (1, -1, 0, 0),
    (1, 0, 0, -1), (1, 1, 0, 0)}

theorem energyA_box : ∀ a ∈ Finset.Icc (-3 : ℤ) 3, ∀ b ∈ Finset.Icc (-3 : ℤ) 3,
    ∀ c ∈ Finset.Icc (-3 : ℤ) 3, ∀ d ∈ Finset.Icc (-3 : ℤ) 3,
      (energyA a b c d = 12 ↔ (a, b, c, d) ∈ shellA) := by
  decide

theorem energyB_box : ∀ a ∈ Finset.Icc (-3 : ℤ) 3, ∀ b ∈ Finset.Icc (-3 : ℤ) 3,
    ∀ c ∈ Finset.Icc (-3 : ℤ) 3, ∀ d ∈ Finset.Icc (-3 : ℤ) 3,
      (energyB a b c d = 12 ↔ (a, b, c, d) ∈ shellB) := by
  decide

/-- Tuples as sectors. -/
def ofTuple (t : ℤ × ℤ × ℤ × ℤ) : Fin 4 → ℤ := ![t.1, t.2.1, t.2.2.1, t.2.2.2]

theorem ofTuple_injective : Function.Injective ofTuple := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [ofTuple] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

theorem eq_ofTuple (x : Fin 4 → ℤ) : x = ofTuple (x 0, x 1, x 2, x 3) := by
  ext i; fin_cases i <;> rfl

/-- **The shell of `schiemannA` at energy `12`.** -/
theorem schiemannA_shell :
    {x : Fin 4 → ℤ | intEnergy schiemannA x = 12} = ↑(shellA.image ofTuple) := by
  ext x
  rw [Set.mem_ofPred_eq, intEnergy_schiemannA, Finset.coe_image, Set.mem_image]
  constructor
  · intro h
    have hb := abs_le_three_of_sq_le
      ((sum_sq_le_energyA (x 0) (x 1) (x 2) (x 3)).trans h.le)
    exact ⟨_, (energyA_box _ hb.1 _ hb.2.1 _ hb.2.2.1 _ hb.2.2.2).1 h,
      (eq_ofTuple x).symm⟩
  · rintro ⟨⟨a, b, c, d⟩, ht, rfl⟩
    have hm := Finset.mem_coe.1 ht
    revert hm
    simp only [shellA, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h | h | h | h | h | h | h) <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;>
      decide

/-- **The shell of `schiemannB` at energy `12`.** -/
theorem schiemannB_shell :
    {x : Fin 4 → ℤ | intEnergy schiemannB x = 12} = ↑(shellB.image ofTuple) := by
  ext x
  rw [Set.mem_ofPred_eq, intEnergy_schiemannB, Finset.coe_image, Set.mem_image]
  constructor
  · intro h
    have h2 := (sum_sq_le_energyB (x 0) (x 1) (x 2) (x 3)).trans h.le
    have hb := abs_le_three_of_sq_le (a := x 0) (b := x 1) (c := x 2) (d := x 3)
      (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)])
    exact ⟨_, (energyB_box _ hb.1 _ hb.2.1 _ hb.2.2.1 _ hb.2.2.2).1 h,
      (eq_ofTuple x).symm⟩
  · rintro ⟨⟨a, b, c, d⟩, ht, rfl⟩
    have hm := Finset.mem_coe.1 ht
    revert hm
    simp only [shellB, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h | h | h | h | h | h | h) <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;>
      decide

/-- Congruence of tuples modulo `2`. -/
def tupleCong (s t : ℤ × ℤ × ℤ × ℤ) : Prop :=
  (2 : ℤ) ∣ s.1 - t.1 ∧ (2 : ℤ) ∣ s.2.1 - t.2.1 ∧ (2 : ℤ) ∣ s.2.2.1 - t.2.2.1 ∧
    (2 : ℤ) ∣ s.2.2.2 - t.2.2.2

instance : DecidableRel tupleCong := fun _ _ => by
  unfold tupleCong; infer_instance

theorem cong_ofTuple_iff (s t : ℤ × ℤ × ℤ × ℤ) :
    (∀ i, (2 : ℤ) ∣ ofTuple s i - ofTuple t i) ↔ tupleCong s t := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption

theorem classPairs_eq_image (G : Matrix (Fin 4) (Fin 4) ℤ) (S : Finset (ℤ × ℤ × ℤ × ℤ))
    (hS : {x : Fin 4 → ℤ | intEnergy G x = 12} = ↑(S.image ofTuple)) :
    classPairs G 12 = ↑(((S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ tupleCong p.1 p.2).image
      fun p => (ofTuple p.1, ofTuple p.2)) := by
  have mem : ∀ x, intEnergy G x = 12 ↔ ∃ s ∈ S, ofTuple s = x := fun x => by
    have := congrArg (x ∈ ·) hS
    simpa using this
  ext ⟨x, y⟩
  rw [Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨hx, hy, hne, hdvd⟩
    obtain ⟨s, hs, rfl⟩ := (mem x).1 hx
    obtain ⟨t, ht, rfl⟩ := (mem y).1 hy
    refine ⟨(s, t), ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hs, ht⟩, fun h => hne (congrArg ofTuple h), (cong_ofTuple_iff s t).1 hdvd⟩
  · rintro ⟨⟨s, t⟩, hst, he⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hst
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨(mem _).2 ⟨s, hst.1.1, rfl⟩, (mem _).2 ⟨t, hst.1.2, rfl⟩,
      fun h => hst.2.1 (ofTuple_injective h), (cong_ofTuple_iff s t).2 hst.2.2⟩

theorem ncard_classPairs (G : Matrix (Fin 4) (Fin 4) ℤ) (S : Finset (ℤ × ℤ × ℤ × ℤ))
    (hS : {x : Fin 4 → ℤ | intEnergy G x = 12} = ↑(S.image ofTuple)) :
    (classPairs G 12).ncard =
      ((S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ tupleCong p.1 p.2).card := by
  rw [classPairs_eq_image G S hS, Set.ncard_coe_finset, Finset.card_image_of_injective]
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only [Prod.mk.injEq] at h
  rw [ofTuple_injective h.1, ofTuple_injective h.2]

/-- **Ten class pairs** for `schiemannA` at energy `12`. -/
theorem schiemannA_classPairs_ncard : (classPairs schiemannA 12).ncard = 10 := by
  rw [ncard_classPairs _ _ schiemannA_shell]
  decide

/-- **Eighteen class pairs** for `schiemannB` at energy `12`. -/
theorem schiemannB_classPairs_ncard : (classPairs schiemannB 12).ncard = 18 := by
  rw [ncard_classPairs _ _ schiemannB_shell]
  decide

/-- **The mod-`2` residue datum separates Schiemann's pair**: no
integral isometry carries `schiemannA` to `schiemannB`. -/
theorem schiemann_not_isometric :
    ¬ ∃ U : GL (Fin 4) ℤ, (U : Matrix (Fin 4) (Fin 4) ℤ)ᵀ * schiemannA *
      (U : Matrix (Fin 4) (Fin 4) ℤ) = schiemannB := by
  rintro ⟨U, hU⟩
  have := classPairs_ncard_eq_of_isometry schiemannA U 12
  rw [hU, schiemannA_classPairs_ncard, schiemannB_classPairs_ncard] at this
  omega

end Theaetetus
