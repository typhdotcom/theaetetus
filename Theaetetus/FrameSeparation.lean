import Theaetetus.SiegelDegree
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Frames: the mod-2 classes of an even lattice at energy 4

Let `G` be a symmetric integral Gram matrix whose energy is even and
positive off zero. Two sectors of energy `4` congruent modulo `2`
are equal, opposite, or orthogonal (`pairing_of_congr_four`): their
half difference has even energy, which pins the pairing to
`{4, 0, −4}`. Choosing a sign per opposite pair (`lexPos`, the sign
of the first nonzero coordinate) leaves an orthogonal family of
anisotropic vectors, linearly independent over `ℚ`, so a class
holds at most `2n` sectors of energy `4` (`frame_card_le`). -/

namespace Theaetetus

open Matrix

variable {n : ℕ}

/-- An even lattice whose energy is positive off zero. -/
structure EvenPosForm (G : Matrix (Fin n) (Fin n) ℤ) : Prop where
  symm : G.IsSymm
  even : ∀ z, (2 : ℤ) ∣ intEnergy G z
  pos : ∀ z, z ≠ 0 → 0 < intEnergy G z

theorem intEnergy_eq_gramPairing (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    intEnergy G x = gramPairing G x x := rfl

theorem intEnergy_neg (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    intEnergy G (-x) = intEnergy G x := by
  simp [intEnergy, mulVec_neg]

theorem intEnergy_zero (G : Matrix (Fin n) (Fin n) ℤ) : intEnergy G 0 = 0 := by
  simp [intEnergy]

theorem intEnergy_sub {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm) (x y : Fin n → ℤ) :
    intEnergy G (x - y) = intEnergy G x + intEnergy G y - 2 * gramPairing G x y := by
  have hc := gramPairing_comm hG x y
  unfold gramPairing at hc
  unfold intEnergy gramPairing
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hc]
  ring

theorem intEnergy_add {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm) (x y : Fin n → ℤ) :
    intEnergy G (x + y) = intEnergy G x + intEnergy G y + 2 * gramPairing G x y := by
  have hc := gramPairing_comm hG x y
  unfold gramPairing at hc
  unfold intEnergy gramPairing
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [hc]
  ring

theorem intEnergy_two_smul (G : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    intEnergy G ((2 : ℤ) • z) = 4 * intEnergy G z := by
  simp only [intEnergy, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- A difference divisible by `2` is twice an integral vector. -/
theorem exists_two_smul_of_dvd {x y : Fin n → ℤ} (h : ∀ i, (2 : ℤ) ∣ x i - y i) :
    ∃ z, x - y = (2 : ℤ) • z :=
  ⟨fun i => (x i - y i) / 2, funext fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' (h i)]⟩

theorem EvenPosForm.energy_nonneg {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    (z : Fin n → ℤ) : 0 ≤ intEnergy G z := by
  by_cases hz : z = 0
  · rw [hz, intEnergy_zero]
  · exact (hG.pos z hz).le

theorem EvenPosForm.eq_zero_of_energy_eq_zero {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : EvenPosForm G) {z : Fin n → ℤ} (h : intEnergy G z = 0) : z = 0 := by
  by_contra hz
  exact (hG.pos z hz).ne' h

/-- **Energy-four sectors in one class are equal, opposite, or
orthogonal.** -/
theorem pairing_of_congr_four {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    {x y : Fin n → ℤ} (hx : intEnergy G x = 4) (hy : intEnergy G y = 4)
    (hc : ∀ i, (2 : ℤ) ∣ x i - y i) :
    x = y ∨ x = -y ∨ gramPairing G x y = 0 := by
  obtain ⟨z, hz⟩ := exists_two_smul_of_dvd hc
  have h1 := intEnergy_sub hG.symm x y
  rw [hz, intEnergy_two_smul, hx, hy] at h1
  have h2 := intEnergy_add hG.symm x y
  rw [hx, hy] at h2
  obtain ⟨k, hk⟩ := hG.even z
  have hz0 := hG.energy_nonneg z
  have hs0 := hG.energy_nonneg (x + y)
  have hk0 : 0 ≤ k := by omega
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · left
    have : z = 0 := hG.eq_zero_of_energy_eq_zero (by omega)
    rw [this, smul_zero] at hz
    exact sub_eq_zero.mp hz
  · right; right; omega
  · right; left
    have : x + y = 0 := hG.eq_zero_of_energy_eq_zero (by omega)
    exact eq_neg_of_add_eq_zero_left this

/-- Lexicographic positivity: the first nonzero coordinate is
positive. -/
def lexPos (x : Fin n → ℤ) : Prop :=
  ∃ i, 0 < x i ∧ ∀ j, j < i → x j = 0

theorem lexPos_or_neg {x : Fin n → ℤ} (hx : x ≠ 0) : lexPos x ∨ lexPos (-x) := by
  classical
  have hne : (Finset.univ.filter fun i => x i ≠ 0).Nonempty := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, by simpa using hi⟩
  set i := (Finset.univ.filter fun i => x i ≠ 0).min' hne
  have hi : x i ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hbelow : ∀ j, j < i → x j = 0 := by
    intro j hj
    by_contra h
    have : i ≤ j := Finset.min'_le _ _ (by simpa using h)
    exact absurd hj (not_lt.mpr this)
  rcases lt_or_gt_of_ne hi with h | h
  · right
    exact ⟨i, by simpa using h, fun j hj => by simp [hbelow j hj]⟩
  · left
    exact ⟨i, h, hbelow⟩

theorem not_lexPos_and_neg (x : Fin n → ℤ) : ¬ (lexPos x ∧ lexPos (-x)) := by
  rintro ⟨⟨i, hi, hbi⟩, ⟨j, hj, hbj⟩⟩
  rcases lt_trichotomy i j with h | rfl | h
  · have := hbj i h; simp at this; omega
  · simp at hj; omega
  · have := hbi j h; simp at hj; omega

theorem castVec_injective : Function.Injective (fun x : Fin n → ℤ => fun i => (x i : ℚ)) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only at this
  exact_mod_cast this

theorem toBilin'_castVec (G : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    Matrix.toBilin' (G.map (Int.cast : ℤ → ℚ)) (fun i => (x i : ℚ)) (fun i => (y i : ℚ))
      = (gramPairing G x y : ℚ) := by
  rw [Matrix.toBilin'_apply']
  simp only [gramPairing, dotProduct, mulVec, map_apply]
  push_cast
  rfl

/-- **The frame bound**: a mod-`2` class of an even positive form on
`ℤⁿ` holds at most `2n` sectors of energy `4`. -/
theorem frame_card_le {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    (S : Finset (Fin n → ℤ)) (hS : ∀ x ∈ S, intEnergy G x = 4)
    (hc : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ x i - y i) :
    S.card ≤ 2 * n := by
  classical
  have hne : ∀ x ∈ S, x ≠ 0 := fun x hx h => by
    have := hS x hx; rw [h, intEnergy_zero] at this; omega
  let f : (Fin n → ℤ) → (Fin n → ℤ) := fun x => if lexPos x then x else -x
  have hfpos : ∀ x ∈ S, lexPos (f x) := fun x hx => by
    by_cases h : lexPos x
    · simp [f, h]
    · simp only [f, h]
      exact (lexPos_or_neg (hne x hx)).resolve_left h
  have hfpm : ∀ x, f x = x ∨ f x = -x := fun x => by
    by_cases h : lexPos x
    · left; simp [f, h]
    · right; simp [f, h]
  set A := S.image f
  -- each fiber has at most two points
  have hfib : S.card ≤ 2 * A.card := by
    refine Finset.card_le_mul_card_image S 2 fun a _ => ?_
    calc (S.filter fun x => f x = a).card ≤ ({a, -a} : Finset _).card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Finset.mem_filter] at hx
          rcases hfpm x with h | h
          · rw [← hx.2, h]; simp
          · have : x = -a := by rw [← hx.2, h, neg_neg]
            simp [this]
      _ ≤ 2 := Finset.card_le_two
  -- the representatives are pairwise orthogonal and anisotropic
  have hA : ∀ a ∈ A, intEnergy G a = 4 ∧ lexPos a ∧ ∃ x ∈ S, a = x ∨ a = -x := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    refine ⟨?_, hfpos x hx, x, hx, hfpm x⟩
    rcases hfpm x with h | h <;> rw [h]
    · exact hS x hx
    · rw [intEnergy_neg]; exact hS x hx
  have hcongA : ∀ a ∈ A, ∀ b ∈ A, ∀ i, (2 : ℤ) ∣ a i - b i := by
    intro a ha b hb i
    obtain ⟨-, -, x, hx, hax⟩ := hA a ha
    obtain ⟨-, -, y, hy, hby⟩ := hA b hb
    have hxy := hc x hx y hy i
    have h2x : (2 : ℤ) ∣ 2 * x i := dvd_mul_right _ _
    have h2y : (2 : ℤ) ∣ 2 * y i := dvd_mul_right _ _
    rcases hax with h1 | h1 <;> rcases hby with h2 | h2 <;> rw [h1, h2]
    · exact hxy
    · have := dvd_add hxy h2y
      rw [show x i - y i + 2 * y i = x i - -y i by ring] at this
      simpa using this
    · have := dvd_sub hxy h2x
      rw [show x i - y i - 2 * x i = -x i - y i by ring] at this
      simpa using this
    · have := dvd_neg.mpr hxy
      rw [show -(x i - y i) = -x i - -y i by ring] at this
      simpa using this
  have horth : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → gramPairing G a b = 0 := by
    intro a ha b hb hab
    obtain ⟨ea, pa, -⟩ := hA a ha
    obtain ⟨eb, pb, -⟩ := hA b hb
    rcases pairing_of_congr_four hG ea eb (hcongA a ha b hb) with h | h | h
    · exact absurd h hab
    · exact absurd ⟨pb, by rw [← h]; exact pa⟩ (not_lexPos_and_neg b)
    · exact h
  -- linear independence over ℚ
  let cast : (Fin n → ℤ) → (Fin n → ℚ) := fun x i => (x i : ℚ)
  set B := Matrix.toBilin' (G.map (Int.cast : ℤ → ℚ))
  have hli : LinearIndependent ℚ (fun v => v : A.image cast → (Fin n → ℚ)) := by
    refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := B) ?_ ?_
    · rw [LinearMap.BilinForm.iIsOrtho_def]
      rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
      have hab : a ≠ b := fun h => huv (by subst h; rfl)
      show B (cast a) (cast b) = 0
      rw [toBilin'_castVec, horth a ha b hb hab]
      simp
    · rintro ⟨u, hu⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      show B (cast a) (cast a) ≠ 0
      rw [toBilin'_castVec, ← intEnergy_eq_gramPairing, (hA a ha).1]
      norm_num
  have hcard := hli.finset_card_le_finrank
  rw [Module.finrank_fin_fun, Finset.card_image_of_injective _ castVec_injective] at hcard
  omega

/-- **Energy-two sectors in one class are equal or opposite.** -/
theorem eq_or_neg_of_congr_two {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    {x y : Fin n → ℤ} (hx : intEnergy G x = 2) (hy : intEnergy G y = 2)
    (hc : ∀ i, (2 : ℤ) ∣ x i - y i) : x = y ∨ x = -y := by
  obtain ⟨z, hz⟩ := exists_two_smul_of_dvd hc
  have h1 := intEnergy_sub hG.symm x y
  rw [hz, intEnergy_two_smul, hx, hy] at h1
  have h2 := intEnergy_add hG.symm x y
  rw [hx, hy] at h2
  obtain ⟨k, hk⟩ := hG.even z
  have hz0 := hG.energy_nonneg z
  have hs0 := hG.energy_nonneg (x + y)
  have hk0 : 0 ≤ k := by omega
  have hk1 : k ≤ 1 := by omega
  interval_cases k
  · left
    have : z = 0 := hG.eq_zero_of_energy_eq_zero (by omega)
    rw [this, smul_zero] at hz
    exact sub_eq_zero.mp hz
  · right
    have : x + y = 0 := hG.eq_zero_of_energy_eq_zero (by omega)
    exact eq_neg_of_add_eq_zero_left this

/-- A nonzero sector of an even positive form has energy at least `2`. -/
theorem EvenPosForm.two_le {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    {z : Fin n → ℤ} (hz : z ≠ 0) : 2 ≤ intEnergy G z := by
  have := hG.pos z hz
  obtain ⟨k, hk⟩ := hG.even z
  omega

/-! ## `E8` and `E8 ⊕ E8` -/

/-- The Cartan matrix of `E8`. -/
def e8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0, 0, 0; -1, 0, 2, -1, 0, 0, 0, 0;
    0, -1, -1, 2, -1, 0, 0, 0; 0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, 0, 0, -1, 2]

/-- The energy of `E8` as a polynomial. -/
def energyE8 (x : Fin 8 → ℤ) : ℤ :=
  2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
    - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7)

theorem intEnergy_e8 (x : Fin 8 → ℤ) : intEnergy e8 x = energyE8 x := by
  simp [intEnergy, e8, energyE8, dotProduct, mulVec, Fin.sum_univ_eight]
  ring

/-- The `LDLᵀ` certificate of `E8`. -/
theorem energyE8_sos (x : Fin 8 → ℤ) :
    (energyE8 x : ℚ) = 2 * ((x 0 : ℚ) - x 2 / 2) ^ 2 + 2 * ((x 1 : ℚ) - x 3 / 2) ^ 2
      + 3 / 2 * ((x 2 : ℚ) - 2 / 3 * x 3) ^ 2 + 5 / 6 * ((x 3 : ℚ) - 6 / 5 * x 4) ^ 2
      + 4 / 5 * ((x 4 : ℚ) - 5 / 4 * x 5) ^ 2 + 3 / 4 * ((x 5 : ℚ) - 4 / 3 * x 6) ^ 2
      + 2 / 3 * ((x 6 : ℚ) - 3 / 2 * x 7) ^ 2 + 1 / 2 * (x 7 : ℚ) ^ 2 := by
  unfold energyE8
  push_cast
  ring

theorem e8_evenPos : EvenPosForm e8 where
  symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  even z := by
    rw [intEnergy_e8]
    exact ⟨_, rfl⟩
  pos z hz := by
    rw [intEnergy_e8]
    by_contra hle
    push Not at hle
    have hq : (energyE8 z : ℚ) ≤ 0 := by exact_mod_cast hle
    rw [energyE8_sos] at hq
    have s0 := sq_nonneg ((z 0 : ℚ) - z 2 / 2)
    have s1 := sq_nonneg ((z 1 : ℚ) - z 3 / 2)
    have s2 := sq_nonneg ((z 2 : ℚ) - 2 / 3 * z 3)
    have s3 := sq_nonneg ((z 3 : ℚ) - 6 / 5 * z 4)
    have s4 := sq_nonneg ((z 4 : ℚ) - 5 / 4 * z 5)
    have s5 := sq_nonneg ((z 5 : ℚ) - 4 / 3 * z 6)
    have s6 := sq_nonneg ((z 6 : ℚ) - 3 / 2 * z 7)
    have s7 := sq_nonneg (z 7 : ℚ)
    have e7 : (z 7 : ℚ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e6 : (z 6 : ℚ) - 3 / 2 * z 7 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e5 : (z 5 : ℚ) - 4 / 3 * z 6 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e4 : (z 4 : ℚ) - 5 / 4 * z 5 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e3 : (z 3 : ℚ) - 6 / 5 * z 4 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e2 : (z 2 : ℚ) - 2 / 3 * z 3 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e1 : (z 1 : ℚ) - z 3 / 2 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e0 : (z 0 : ℚ) - z 2 / 2 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have q6 : (z 6 : ℚ) = 0 := by linarith
    have q5 : (z 5 : ℚ) = 0 := by linarith
    have q4 : (z 4 : ℚ) = 0 := by linarith
    have q3 : (z 3 : ℚ) = 0 := by linarith
    have q2 : (z 2 : ℚ) = 0 := by linarith
    have q1 : (z 1 : ℚ) = 0 := by linarith
    have q0 : (z 0 : ℚ) = 0 := by linarith
    apply hz
    funext i
    have h : ∀ j, (z j : ℚ) = 0 := by
      intro j
      fin_cases j
      exacts [q0, q1, q2, q3, q4, q5, q6, e7]
    exact_mod_cast h i

/-- The Gram matrix of `E8 ⊕ E8`. -/
def e8sq : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks e8 0 0 e8)

/-- The first summand of a sector of `E8 ⊕ E8`. -/
def lft (x : Fin 16 → ℤ) : Fin 8 → ℤ := fun i => x (Fin.castAdd 8 i)

/-- The second summand of a sector of `E8 ⊕ E8`. -/
def rgt (x : Fin 16 → ℤ) : Fin 8 → ℤ := fun i => x (Fin.natAdd 8 i)

theorem intEnergy_e8sq (x : Fin 16 → ℤ) :
    intEnergy e8sq x = intEnergy e8 (lft x) + intEnergy e8 (rgt x) := by
  have hx : x ∘ finSumFinEquiv = Sum.elim (lft x) (rgt x) := by
    funext s; cases s <;> rfl
  have hv : e8sq *ᵥ x = (Matrix.fromBlocks e8 0 0 e8 *ᵥ (x ∘ finSumFinEquiv))
      ∘ finSumFinEquiv.symm := by
    rw [e8sq, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  unfold intEnergy
  rw [hv, dotProduct_comp_equiv_symm, hx, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  rw [sumElim_dotProduct_sumElim]
  rfl

theorem eq_of_lft_rgt {x y : Fin 16 → ℤ} (h1 : lft x = lft y) (h2 : rgt x = rgt y) :
    x = y := by
  funext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i
  · exact congrFun h1 j
  · exact congrFun h2 j

theorem lft_eq_zero_of_even {x : Fin 16 → ℤ} (hx : intEnergy e8sq x = 4)
    (he : ∀ i, (2 : ℤ) ∣ lft x i) : lft x = 0 := by
  obtain ⟨w, hw⟩ := exists_two_smul_of_dvd (x := lft x) (y := 0) (by simpa using he)
  rw [sub_zero] at hw
  have hsplit := intEnergy_e8sq x
  rw [hw, intEnergy_two_smul] at hsplit
  have hr := e8_evenPos.energy_nonneg (rgt x)
  have hw0 : w = 0 := by
    by_contra h
    have := e8_evenPos.two_le h
    omega
  rw [hw, hw0, smul_zero]

theorem rgt_eq_zero_of_even {x : Fin 16 → ℤ} (hx : intEnergy e8sq x = 4)
    (he : ∀ i, (2 : ℤ) ∣ rgt x i) : rgt x = 0 := by
  obtain ⟨w, hw⟩ := exists_two_smul_of_dvd (x := rgt x) (y := 0) (by simpa using he)
  rw [sub_zero] at hw
  have hsplit := intEnergy_e8sq x
  rw [hw, intEnergy_two_smul] at hsplit
  have hl := e8_evenPos.energy_nonneg (lft x)
  have hw0 : w = 0 := by
    by_contra h
    have := e8_evenPos.two_le h
    omega
  rw [hw, hw0, smul_zero]

/-- **The frame bound of `E8 ⊕ E8`**: a mod-`2` class holds at most `16`
sectors of energy `4`. Either one summand vanishes on the class, and
the other is an `E8` frame; or both summands are roots, determined up
to sign. -/
theorem e8sq_class_card_le (S : Finset (Fin 16 → ℤ)) (hS : ∀ x ∈ S, intEnergy e8sq x = 4)
    (hc : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ x i - y i) : S.card ≤ 16 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp
  have hcl : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ lft x i - lft y i :=
    fun x hx y hy i => hc x hx y hy _
  have hcr : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ rgt x i - rgt y i :=
    fun x hx y hy i => hc x hx y hy _
  by_cases hL : ∀ i, (2 : ℤ) ∣ lft x0 i
  · -- the first summand vanishes on the class
    have hl0 : ∀ x ∈ S, lft x = 0 := fun x hx => lft_eq_zero_of_even (hS x hx) fun i => by
      have := dvd_add (hcl x hx x0 hx0 i) (hL i)
      simpa using this
    have hinj : Set.InjOn rgt S := fun x hx y hy h =>
      eq_of_lft_rgt (by rw [hl0 x hx, hl0 y hy]) h
    rw [← Finset.card_image_of_injOn hinj]
    refine frame_card_le e8_evenPos _ (fun v hv => ?_) (fun v hv w hw i => ?_)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      have := intEnergy_e8sq x
      rw [hl0 x hx, intEnergy_zero, hS x hx] at this
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
      exact hcr x hx y hy i
  by_cases hR : ∀ i, (2 : ℤ) ∣ rgt x0 i
  · -- the second summand vanishes on the class
    have hr0 : ∀ x ∈ S, rgt x = 0 := fun x hx => rgt_eq_zero_of_even (hS x hx) fun i => by
      have := dvd_add (hcr x hx x0 hx0 i) (hR i)
      simpa using this
    have hinj : Set.InjOn lft S := fun x hx y hy h =>
      eq_of_lft_rgt h (by rw [hr0 x hx, hr0 y hy])
    rw [← Finset.card_image_of_injOn hinj]
    refine frame_card_le e8_evenPos _ (fun v hv => ?_) (fun v hv w hw i => ?_)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      have := intEnergy_e8sq x
      rw [hr0 x hx, intEnergy_zero, hS x hx] at this
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
      exact hcl x hx y hy i
  -- both summands are roots, each determined up to sign
  have hroots : ∀ x ∈ S, intEnergy e8 (lft x) = 2 ∧ intEnergy e8 (rgt x) = 2 := by
    intro x hx
    have hlx : lft x ≠ 0 := by
      intro h
      apply hL
      intro i
      have := hcl x0 hx0 x hx i
      rw [h] at this
      simpa using this
    have hrx : rgt x ≠ 0 := by
      intro h
      apply hR
      intro i
      have := hcr x0 hx0 x hx i
      rw [h] at this
      simpa using this
    have h2l := e8_evenPos.two_le hlx
    have h2r := e8_evenPos.two_le hrx
    have := intEnergy_e8sq x
    rw [hS x hx] at this
    omega
  have himg : S.image (fun x => (lft x, rgt x))
      ⊆ ({lft x0, -lft x0} : Finset _) ×ˢ ({rgt x0, -rgt x0} : Finset _) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    rw [Finset.mem_product]
    constructor
    · rcases eq_or_neg_of_congr_two e8_evenPos (hroots x hx).1 (hroots x0 hx0).1
        (hcl x hx x0 hx0) with h | h <;> simp [h]
    · rcases eq_or_neg_of_congr_two e8_evenPos (hroots x hx).2 (hroots x0 hx0).2
        (hcr x hx x0 hx0) with h | h <;> simp [h]
  have hinj : Set.InjOn (fun x => (lft x, rgt x)) S := fun x _ y _ h => by
    simp only [Prod.mk.injEq] at h
    exact eq_of_lft_rgt h.1 h.2
  rw [← Finset.card_image_of_injOn hinj]
  calc _ ≤ (({lft x0, -lft x0} : Finset _) ×ˢ ({rgt x0, -rgt x0} : Finset _)).card :=
        Finset.card_le_card himg
    _ ≤ 2 * 2 := by
        rw [Finset.card_product]
        exact Nat.mul_le_mul Finset.card_le_two Finset.card_le_two
    _ ≤ 16 := by norm_num

/-! ## `D16⁺` -/

/-- A Gram matrix of `D16⁺`: the `D16` basis with `e1 − e2` replaced by
the glue `(1/2)^16`. -/
def d16plus : Matrix (Fin 16) (Fin 16) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, -1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4]

/-- The sectors `±2eᵢ` of `D16⁺` in that basis. -/
def d16frame : List (Fin 16 → ℤ) :=
  [![-2, -4, -6, -8, -10, -12, -14, -16, -18, -20, -22, -24, -26, -13, -15, 4],
   ![2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 13, 15, -4],
   ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![-2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, -2, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0],
   ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]]

theorem d16frame_energy : ∀ v ∈ d16frame, intEnergy d16plus v = 4 := by decide

theorem d16frame_cong : ∀ v ∈ d16frame, ∀ w ∈ d16frame, ∀ i, (2 : ℤ) ∣ v i - w i := by
  decide

theorem d16frame_card : d16frame.toFinset.card = 32 := by decide

/-- **`D16⁺` has a full frame in one class**: the 32 sectors `±2eᵢ`
have energy `4` and are congruent modulo `2`. -/
theorem d16plus_frame :
    ∃ S : Finset (Fin 16 → ℤ), S.card = 32 ∧ (∀ x ∈ S, intEnergy d16plus x = 4) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ x i - y i :=
  ⟨d16frame.toFinset, d16frame_card,
    fun x hx => d16frame_energy x (List.mem_toFinset.1 hx),
    fun x hx y hy => d16frame_cong x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy)⟩

/-- **The frame separation**: no integral isometry carries `E8 ⊕ E8`
to `D16⁺`. An isometry carries the 32-sector class of `D16⁺` into one
class of `E8 ⊕ E8`, which holds at most 16. -/
theorem e8sq_not_isometric_d16plus :
    ¬ ∃ U : GL (Fin 16) ℤ, (U : Matrix (Fin 16) (Fin 16) ℤ)ᵀ * e8sq *
      (U : Matrix (Fin 16) (Fin 16) ℤ) = d16plus := by
  classical
  rintro ⟨U, hU⟩
  obtain ⟨S, hcard, hS, hc⟩ := d16plus_frame
  set V : Matrix (Fin 16) (Fin 16) ℤ := ↑U
  set W : Matrix (Fin 16) (Fin 16) ℤ := ↑(U⁻¹ : GL (Fin 16) ℤ)
  have hWV : W * V = 1 := by simp [V, W]
  have hinj : Set.InjOn (fun x => V *ᵥ x) S := fun x _ y _ h => by
    have := congrArg (W *ᵥ ·) h
    simpa [mulVec_mulVec, hWV] using this
  have hle := e8sq_class_card_le (S.image fun x => V *ᵥ x)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      rw [intEnergy_mulVec, hU]
      exact hS x hx)
    (fun v hv w hw i => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
      exact two_dvd_mulVec_sub V (hc x hx y hy) i)
  rw [Finset.card_image_of_injOn hinj, hcard] at hle
  omega

end Theaetetus
