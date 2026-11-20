import Theaetetus.CosetSeparation

/-! # Class pairs are degree-two Siegel data

For a symmetric positive-definite integral Gram matrix `G`, a pair of
distinct sectors `x, x′` of energy `m` congruent modulo `2` is the
same thing as a pair `(x, y)` with `x′ = x + 2y`: the energy of
`x + 2y` is `Q(x) + 4⟨x, y⟩ + 4Q(y)` (`intEnergy_add_two_smul`), so
the class condition is the Gram condition
`Q(x) = m`, `⟨x, y⟩ = −Q(y)`, `Q(y) ≠ 0`. Sorting by `t = Q(y)`
identifies the class pairs with the disjoint union, over `t ≠ 0`, of
the degree-two representation sets of the binary Gram matrices
`!![m, −t; −t, t]` (`classPairsEquivSigma`).

Hence equal degree-two representation numbers force equal class-pair
counts (`classPairs_ncard_eq_of_siegelSet`), and the separation of
Schiemann's pair by class pairs is a separation by degree-two
representation numbers: some binary Gram matrix is represented by
`schiemannA` and `schiemannB` in non-equinumerous ways
(`schiemann_siegelSet_ne`). -/

namespace Theaetetus

open Matrix

variable {n : ℕ}

/-- The integral bilinear form `xᵀ G y`. -/
def gramPairing (G : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) : ℤ :=
  x ⬝ᵥ G *ᵥ y

/-- The degree-two representation set of a binary Gram matrix `T`:
pairs of sectors with Gram matrix `T`. -/
def siegelSet (G : Matrix (Fin n) (Fin n) ℤ) (T : Matrix (Fin 2) (Fin 2) ℤ) :
    Set (Fin 2 → Fin n → ℤ) :=
  {X | ∀ i j, gramPairing G (X i) (X j) = T i j}

/-- The binary Gram matrix of a class pair at energy `m`, sorted by
the energy `t` of its half difference. -/
def pairGram (m t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![m, -t; -t, t]

theorem gramPairing_comm {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (x y : Fin n → ℤ) : gramPairing G y x = gramPairing G x y := by
  unfold gramPairing
  rw [dotProduct_mulVec, ← mulVec_transpose, hG.eq, dotProduct_comm]

theorem intEnergy_add_two_smul {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (x y : Fin n → ℤ) :
    intEnergy G (x + (2 : ℤ) • y)
      = intEnergy G x + 4 * gramPairing G x y + 4 * intEnergy G y := by
  have hc := gramPairing_comm hG x y
  unfold gramPairing at hc
  unfold intEnergy gramPairing
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hc]
  ring

/-- The Gram condition on a pair `(x, y)` carrying a class pair. -/
def pairCond (G : Matrix (Fin n) (Fin n) ℤ) (m : ℤ) (X : Fin 2 → Fin n → ℤ) : Prop :=
  intEnergy G (X 0) = m ∧ gramPairing G (X 0) (X 1) = -intEnergy G (X 1) ∧
    intEnergy G (X 1) ≠ 0

/-- Class pairs are pairs `(x, y)` under the Gram condition. -/
def classPairsEquivCond {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (hpos : ∀ y, y ≠ 0 → 0 < intEnergy G y) (m : ℤ) :
    classPairs G m ≃ {X : Fin 2 → Fin n → ℤ // pairCond G m X} where
  toFun p := ⟨![p.1.1, fun i => (p.1.2 i - p.1.1 i) / 2], by
    obtain ⟨⟨x, x'⟩, hx, hx', hne, hdvd⟩ := p
    set y : Fin n → ℤ := fun i => (x' i - x i) / 2
    have hy : x' = x + (2 : ℤ) • y := by
      funext i
      have : (2 : ℤ) ∣ x' i - x i := by
        have := hdvd i
        rw [← dvd_neg, neg_sub] at this
        exact this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [Int.mul_ediv_cancel' this]
      ring
    have hy0 : y ≠ 0 := by
      rintro h
      exact hne (by rw [hy, h, smul_zero, add_zero])
    refine ⟨?_, ?_, (hpos y hy0).ne'⟩
    · simpa using hx
    · have h := intEnergy_add_two_smul hG x y
      rw [← hy, hx', hx] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith⟩
  invFun X := ⟨(X.1 0, X.1 0 + (2 : ℤ) • X.1 1), by
    obtain ⟨X, h0, h1, h2⟩ := X
    refine ⟨h0, ?_, ?_, ?_⟩
    · show intEnergy G (X 0 + (2 : ℤ) • X 1) = m
      rw [intEnergy_add_two_smul hG, h0, h1]
      ring
    · intro h
      have h' : (2 : ℤ) • X 1 = 0 := by
        have := congrArg (· - X 0) h
        simpa using this.symm
      have : X 1 = 0 := by
        funext i
        have := congrFun h' i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        simpa using this
      exact h2 (by rw [this]; simp [intEnergy])
    · intro i
      show (2 : ℤ) ∣ X 0 i - (X 0 i + 2 * X 1 i)
      exact ⟨-X 1 i, by ring⟩⟩
  left_inv p := by
    obtain ⟨⟨x, x'⟩, hx, hx', hne, hdvd⟩ := p
    apply Subtype.ext
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.injEq, true_and]
    funext i
    have : (2 : ℤ) ∣ x' i - x i := by
      have := hdvd i
      rw [← dvd_neg, neg_sub] at this
      exact this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' this]
    ring
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    apply Subtype.ext
    funext k i
    fin_cases k
    · rfl
    · simp

/-- The Gram condition at a fixed half-difference energy `t` is
membership in the representation set of `pairGram m t`. -/
theorem pairCond_and_iff {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm) {m t : ℤ}
    (ht : t ≠ 0) (X : Fin 2 → Fin n → ℤ) :
    (pairCond G m X ∧ intEnergy G (X 1) = t) ↔ X ∈ siegelSet G (pairGram m t) := by
  constructor
  · rintro ⟨⟨h0, h1, -⟩, ht'⟩ i j
    fin_cases i <;> fin_cases j
    · simpa [pairGram, intEnergy, gramPairing] using h0
    · simpa [pairGram, ht'] using h1
    · rw [gramPairing_comm hG]; simpa [pairGram, ht'] using h1
    · simpa [pairGram, intEnergy, gramPairing] using ht'
  · intro h
    have h00 := h 0 0
    have h01 := h 0 1
    have h11 := h 1 1
    simp only [pairGram, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one] at h00 h01 h11
    have e1 : intEnergy G (X 1) = t := h11
    refine ⟨⟨h00, ?_, by rw [e1]; exact ht⟩, e1⟩
    rw [e1]; exact h01

/-- **Class pairs sorted by half-difference energy**: the class pairs
at energy `m` are the disjoint union over `t ≠ 0` of the degree-two
representation sets of `pairGram m t`. -/
def classPairsEquivSigma {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (hpos : ∀ y, y ≠ 0 → 0 < intEnergy G y) (m : ℤ) :
    classPairs G m ≃ Σ t : {t : ℤ // t ≠ 0}, siegelSet G (pairGram m t) :=
  (classPairsEquivCond hG hpos m).trans <|
    (Equiv.sigmaFiberEquiv (fun X : {X // pairCond G m X} =>
        (⟨intEnergy G (X.1 1), X.2.2.2⟩ : {t : ℤ // t ≠ 0}))).symm.trans <|
      Equiv.sigmaCongrRight fun t =>
        { toFun := fun X => ⟨X.1.1,
            (pairCond_and_iff hG t.2 _).1 ⟨X.1.2, congrArg Subtype.val X.2⟩⟩
          invFun := fun X => ⟨⟨X.1, ((pairCond_and_iff hG t.2 _).2 X.2).1⟩,
            Subtype.ext ((pairCond_and_iff hG t.2 _).2 X.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

/-- **Equal degree-two representation numbers force equal class-pair
counts.** -/
theorem classPairs_ncard_eq_of_siegelSet {G G' : Matrix (Fin n) (Fin n) ℤ}
    (hG : G.IsSymm) (hG' : G'.IsSymm)
    (hpos : ∀ y, y ≠ 0 → 0 < intEnergy G y) (hpos' : ∀ y, y ≠ 0 → 0 < intEnergy G' y)
    (h : ∀ T, Nonempty (siegelSet G T ≃ siegelSet G' T)) (m : ℤ) :
    (classPairs G m).ncard = (classPairs G' m).ncard := by
  rw [Set.ncard_def, Set.ncard_def]
  exact Nat.card_congr ((classPairsEquivSigma hG hpos m).trans <|
    (Equiv.sigmaCongrRight (β₁ := fun t : {t : ℤ // t ≠ 0} => siegelSet G (pairGram m t))
      fun t => (h (pairGram m t)).some).trans
      (classPairsEquivSigma hG' hpos' m).symm)

theorem schiemannA_isSymm : schiemannA.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem schiemannB_isSymm : schiemannB.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem intEnergy_pos_of_sum_sq_le {G : Matrix (Fin 4) (Fin 4) ℤ} {E : ℤ → ℤ → ℤ → ℤ → ℤ}
    (hE : ∀ x : Fin 4 → ℤ, intEnergy G x = E (x 0) (x 1) (x 2) (x 3))
    (hsq : ∀ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ E a b c d)
    (y : Fin 4 → ℤ) (hy : y ≠ 0) : 0 < intEnergy G y := by
  rw [hE]
  refine lt_of_lt_of_le ?_ (hsq _ _ _ _)
  by_contra hle
  push Not at hle
  apply hy
  funext i
  have s0 := sq_nonneg (y 0)
  have s1 := sq_nonneg (y 1)
  have s2 := sq_nonneg (y 2)
  have s3 := sq_nonneg (y 3)
  have h0 : y 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have h1 : y 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have h2 : y 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  have h3 : y 3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
  fin_cases i <;> simp [h0, h1, h2, h3]

/-- **Schiemann's pair has distinct degree-two representation
numbers**: some binary Gram matrix is represented by `schiemannA`
and `schiemannB` in non-equinumerous ways. -/
theorem schiemann_siegelSet_ne :
    ∃ T, IsEmpty (siegelSet schiemannA T ≃ siegelSet schiemannB T) := by
  by_contra h
  push Not at h
  have hA := intEnergy_pos_of_sum_sq_le intEnergy_schiemannA sum_sq_le_energyA
  have hB := intEnergy_pos_of_sum_sq_le intEnergy_schiemannB fun a b c d => by
    nlinarith [sum_sq_le_energyB a b c d, sq_nonneg a, sq_nonneg b, sq_nonneg c,
      sq_nonneg d]
  have := classPairs_ncard_eq_of_siegelSet schiemannA_isSymm schiemannB_isSymm hA hB
    (fun T => h T) 12
  rw [schiemannA_classPairs_ncard, schiemannB_classPairs_ncard] at this
  omega

end Theaetetus
