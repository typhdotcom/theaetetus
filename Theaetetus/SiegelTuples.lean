import Theaetetus.FrameSeparation

/-! # Class tuples are Siegel data, in every degree

For a symmetric positive-definite integral Gram matrix `G`, the
**class tuples** `classTuples G m k` are the injective `k`-tuples of
sectors of energy `m`, pairwise congruent modulo `2`: the `k`-th
falling moment of the per-class counts at energy `m`. Writing a
`(k+1)`-tuple as its first sector `x` and half differences
`yᵢ = (xᵢ − x)/2`, every condition becomes a condition on the Gram
matrix of `(x, y₁, …, y_k)` (`tuplePred`): the energies through
`Q(x + 2y) = Q(x) + 4⟨x,y⟩ + 4Q(y)`, distinctness from `x` through
`Q(yᵢ) ≠ 0`, and mutual distinctness through
`Q(yᵢ − yⱼ) = Q(yᵢ) + Q(yⱼ) − 2⟨yᵢ,yⱼ⟩ ≠ 0` — positive definiteness
makes vanishing energy mean vanishing vector
(`classTuplesEquivPred`).

Any Gram-predicate set is the disjoint union of the degree-`(k+1)`
representation sets of the matrices satisfying it
(`gramFiberEquiv`), so equal representation numbers in degree `k+1`
force equivalent class tuples (`classTuplesEquivOfSiegel`).

Applied to the frame separation: `D16⁺` has 17 distinct energy-four
sectors in one class and `E8 ⊕ E8` cannot
(`e8sq_classTuples_isEmpty`, `d16plus_classTuples_nonempty`), so the
two theta-equivalent lattices have different representation numbers
in degree 17 (`e8sq_d16plus_siegel_ne`). -/

namespace Theaetetus

open Matrix

variable {n k : ℕ}

/-- The Gram matrix of a tuple of sectors. -/
def tupleGram (G : Matrix (Fin n) (Fin n) ℤ) (Y : Fin k → Fin n → ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => gramPairing G (Y i) (Y j)

/-- The degree-`k` representation set of a Gram matrix `T`. -/
def siegelSetK (G : Matrix (Fin n) (Fin n) ℤ) (T : Matrix (Fin k) (Fin k) ℤ) :
    Set (Fin k → Fin n → ℤ) :=
  {Y | tupleGram G Y = T}

/-- Injective `k`-tuples of sectors of energy `m`, pairwise congruent
modulo `2`. -/
def classTuples (G : Matrix (Fin n) (Fin n) ℤ) (m : ℤ) (k : ℕ) : Set (Fin k → Fin n → ℤ) :=
  {X | (∀ i, intEnergy G (X i) = m) ∧ Function.Injective X ∧
    ∀ i j l, (2 : ℤ) ∣ X i l - X j l}

/-- **Gram-predicate sets are sorted by their Gram matrix.** -/
def gramFiberEquiv (G : Matrix (Fin n) (Fin n) ℤ) (P : Matrix (Fin k) (Fin k) ℤ → Prop) :
    {Y : Fin k → Fin n → ℤ // P (tupleGram G Y)} ≃ Σ T : {T // P T}, siegelSetK G T.1 :=
  (Equiv.sigmaFiberEquiv (fun Y : {Y // P (tupleGram G Y)} =>
      (⟨tupleGram G Y.1, Y.2⟩ : {T // P T}))).symm.trans <|
    Equiv.sigmaCongrRight fun T =>
      { toFun := fun Y => ⟨Y.1.1, congrArg Subtype.val Y.2⟩
        invFun := fun Y => ⟨⟨Y.1, by
            have h : tupleGram G Y.1 = T.1 := Y.2
            rw [h]; exact T.2⟩, Subtype.ext Y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

/-- The Gram conditions of a class tuple, in first-sector and
half-difference coordinates. -/
def tuplePred (m : ℤ) (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) : Prop :=
  T 0 0 = m ∧ (∀ i : Fin k, T 0 0 + 4 * T 0 i.succ + 4 * T i.succ i.succ = m) ∧
    (∀ i : Fin k, T i.succ i.succ ≠ 0) ∧
    ∀ i j : Fin k, i ≠ j → T i.succ i.succ + T j.succ j.succ - 2 * T i.succ j.succ ≠ 0

/-- The half difference of two congruent sectors. -/
def halfDiff (a b : Fin n → ℤ) : Fin n → ℤ := fun l => (a l - b l) / 2

theorem eq_add_two_smul_halfDiff {a b : Fin n → ℤ} (h : ∀ l, (2 : ℤ) ∣ a l - b l) :
    a = b + (2 : ℤ) • halfDiff a b := by
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, halfDiff]
  rw [Int.mul_ediv_cancel' (h l)]
  ring

theorem two_smul_injective : Function.Injective (fun y : Fin n → ℤ => (2 : ℤ) • y) := by
  intro y y' h
  funext l
  have := congrFun h l
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega

/-- The coordinates of a class tuple. -/
def tupleCoords (X : Fin (k + 1) → Fin n → ℤ) : Fin (k + 1) → Fin n → ℤ :=
  Fin.cons (X 0) fun i => halfDiff (X i.succ) (X 0)

/-- The class tuple of coordinates. -/
def coordsTuple (Y : Fin (k + 1) → Fin n → ℤ) : Fin (k + 1) → Fin n → ℤ :=
  Fin.cons (Y 0) fun i => Y 0 + (2 : ℤ) • Y i.succ

theorem coordsTuple_zero (Y : Fin (k + 1) → Fin n → ℤ) : coordsTuple Y 0 = Y 0 := rfl

theorem coordsTuple_succ (Y : Fin (k + 1) → Fin n → ℤ) (i : Fin k) :
    coordsTuple Y i.succ = Y 0 + (2 : ℤ) • Y i.succ := rfl

theorem tupleCoords_coordsTuple (Y : Fin (k + 1) → Fin n → ℤ) :
    tupleCoords (coordsTuple Y) = Y := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  funext l
  simp only [tupleCoords, Fin.cons_succ, coordsTuple_succ, coordsTuple_zero, halfDiff,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  omega

theorem coordsTuple_tupleCoords {X : Fin (k + 1) → Fin n → ℤ}
    (hc : ∀ i j l, (2 : ℤ) ∣ X i l - X j l) : coordsTuple (tupleCoords X) = X := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  rw [coordsTuple_succ]
  exact (eq_add_two_smul_halfDiff (hc i.succ 0)).symm

theorem coordsTuple_cong (Y : Fin (k + 1) → Fin n → ℤ) (i j : Fin (k + 1)) (l : Fin n) :
    (2 : ℤ) ∣ coordsTuple Y i l - coordsTuple Y j l := by
  have key : ∀ i, ∃ w : Fin n → ℤ, coordsTuple Y i = Y 0 + (2 : ℤ) • w := fun i =>
    Fin.cases ⟨0, by rw [coordsTuple_zero, smul_zero, add_zero]⟩
      (fun i => ⟨Y i.succ, coordsTuple_succ Y i⟩) i
  obtain ⟨w, hw⟩ := key i
  obtain ⟨w', hw'⟩ := key j
  rw [hw, hw']
  exact ⟨w l - w' l, by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩

theorem coordsTuple_injective {G : Matrix (Fin n) (Fin n) ℤ} {Y : Fin (k + 1) → Fin n → ℤ}
    (hz : ∀ i : Fin k, intEnergy G (Y i.succ) ≠ 0)
    (hd : ∀ i j : Fin k, i ≠ j → intEnergy G (Y i.succ - Y j.succ) ≠ 0) :
    Function.Injective (coordsTuple Y) := by
  have hz' : ∀ i : Fin k, Y i.succ ≠ 0 := fun i h => hz i (by rw [h, intEnergy_zero])
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      rw [coordsTuple_zero, coordsTuple_succ] at h
      exact absurd (two_smul_injective (by simpa using h.symm : (2 : ℤ) • Y j.succ =
        (2 : ℤ) • 0)) (hz' j)
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [coordsTuple_zero, coordsTuple_succ] at h
      exact absurd (two_smul_injective (by simpa using h : (2 : ℤ) • Y i.succ =
        (2 : ℤ) • 0)) (hz' i)
    | succ j =>
      rw [coordsTuple_succ, coordsTuple_succ] at h
      have hy : Y i.succ = Y j.succ := two_smul_injective (add_left_cancel h)
      by_contra hij
      exact hd i j (fun e => hij (by rw [e])) (by rw [hy, sub_self, intEnergy_zero])

/-- **Class tuples are Gram data.** -/
def classTuplesEquivPred {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (hpos : ∀ y, y ≠ 0 → 0 < intEnergy G y) (m : ℤ) :
    classTuples G m (k + 1) ≃ {Y : Fin (k + 1) → Fin n → ℤ // tuplePred m (tupleGram G Y)} where
  toFun X := ⟨tupleCoords X.1, by
    obtain ⟨X, hE, hinj, hc⟩ := X
    have hX : ∀ i : Fin k, X i.succ = X 0 + (2 : ℤ) • halfDiff (X i.succ) (X 0) :=
      fun i => eq_add_two_smul_halfDiff (hc i.succ 0)
    have hne : ∀ i : Fin k, halfDiff (X i.succ) (X 0) ≠ 0 := fun i h => by
      have := hX i
      rw [h, smul_zero, add_zero] at this
      exact Fin.succ_ne_zero i (hinj this)
    refine ⟨?_, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · show gramPairing G (X 0) (X 0) = m
      exact hE 0
    · show gramPairing G (X 0) (X 0) + 4 * gramPairing G (X 0) (halfDiff (X i.succ) (X 0))
          + 4 * gramPairing G (halfDiff (X i.succ) (X 0)) (halfDiff (X i.succ) (X 0)) = m
      have h := intEnergy_add_two_smul hG (X 0) (halfDiff (X i.succ) (X 0))
      rw [← hX i, hE, hE 0] at h
      rw [← intEnergy_eq_gramPairing, ← intEnergy_eq_gramPairing, hE 0]
      linarith
    · show gramPairing G (halfDiff (X i.succ) (X 0)) (halfDiff (X i.succ) (X 0)) ≠ 0
      rw [← intEnergy_eq_gramPairing]
      exact (hpos _ (hne i)).ne'
    · show gramPairing G (halfDiff (X i.succ) (X 0)) (halfDiff (X i.succ) (X 0))
          + gramPairing G (halfDiff (X j.succ) (X 0)) (halfDiff (X j.succ) (X 0))
          - 2 * gramPairing G (halfDiff (X i.succ) (X 0)) (halfDiff (X j.succ) (X 0)) ≠ 0
      rw [← intEnergy_eq_gramPairing, ← intEnergy_eq_gramPairing, ← intEnergy_sub hG]
      refine (hpos _ fun h => ?_).ne'
      have hij' : halfDiff (X i.succ) (X 0) = halfDiff (X j.succ) (X 0) := sub_eq_zero.mp h
      have : X i.succ = X j.succ := by rw [hX i, hX j, hij']
      exact hij (Fin.succ_injective _ (hinj this))⟩
  invFun Y := ⟨coordsTuple Y.1, by
    obtain ⟨Y, h0, hE, hz, hd⟩ := Y
    have h0' : intEnergy G (Y 0) = m := h0
    have hz' : ∀ i : Fin k, intEnergy G (Y i.succ) ≠ 0 := hz
    have hd' : ∀ i j : Fin k, i ≠ j → intEnergy G (Y i.succ - Y j.succ) ≠ 0 := by
      intro i j hij
      rw [intEnergy_sub hG]
      exact hd i j hij
    refine ⟨fun i => ?_, coordsTuple_injective hz' hd', coordsTuple_cong Y⟩
    induction i using Fin.cases with
    | zero => exact h0'
    | succ i =>
      have h := hE i
      change gramPairing G (Y 0) (Y 0) + 4 * gramPairing G (Y 0) (Y i.succ)
        + 4 * gramPairing G (Y i.succ) (Y i.succ) = m at h
      rw [← intEnergy_eq_gramPairing, ← intEnergy_eq_gramPairing, h0'] at h
      rw [coordsTuple_succ, intEnergy_add_two_smul hG, h0']
      exact h⟩
  left_inv X := Subtype.ext (coordsTuple_tupleCoords X.2.2.2)
  right_inv Y := Subtype.ext (tupleCoords_coordsTuple Y.1)

/-- **Equal representation numbers in degree `k + 1` force equivalent
class tuples.** -/
noncomputable def classTuplesEquivOfSiegel {G G' : Matrix (Fin n) (Fin n) ℤ}
    (hG : G.IsSymm) (hG' : G'.IsSymm)
    (hpos : ∀ y, y ≠ 0 → 0 < intEnergy G y) (hpos' : ∀ y, y ≠ 0 → 0 < intEnergy G' y)
    (h : ∀ T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ,
      Nonempty (siegelSetK G T ≃ siegelSetK G' T)) (m : ℤ) :
    classTuples G m (k + 1) ≃ classTuples G' m (k + 1) :=
  (classTuplesEquivPred hG hpos m).trans <| (gramFiberEquiv G (tuplePred m)).trans <|
    (Equiv.sigmaCongrRight (β₁ := fun T : {T // tuplePred m T} => siegelSetK G T.1)
      fun T => (h T.1).some).trans <|
      (gramFiberEquiv G' (tuplePred m)).symm.trans (classTuplesEquivPred hG' hpos' m).symm

/-! ## Degree seventeen separates `E8 ⊕ E8` from `D16⁺` -/

/-- The energy of `D16⁺` as a polynomial. -/
def energyD16 (x : Fin 16 → ℤ) : ℤ :=
  2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 - 2 * x 1 * x 2 + 2 * x 2 ^ 2 - 2 * x 2 * x 3 + 2 * x 3 ^ 2 - 2 * x 3 * x 4 + 2 * x 4 ^ 2 - 2 * x 4 * x 5 + 2 * x 5 ^ 2 - 2 * x 5 * x 6 + 2 * x 6 ^ 2 - 2 * x 6 * x 7 + 2 * x 7 ^ 2 - 2 * x 7 * x 8 + 2 * x 8 ^ 2 - 2 * x 8 * x 9 + 2 * x 9 ^ 2 - 2 * x 9 * x 10 + 2 * x 10 ^ 2 - 2 * x 10 * x 11 + 2 * x 11 ^ 2 - 2 * x 11 * x 12 + 2 * x 12 ^ 2 - 2 * x 12 * x 13 - 2 * x 12 * x 14 + 2 * x 13 ^ 2 + 2 * x 14 ^ 2 + 2 * x 14 * x 15 + 4 * x 15 ^ 2

theorem intEnergy_d16plus (x : Fin 16 → ℤ) : intEnergy d16plus x = energyD16 x := by
  simp [intEnergy, d16plus, energyD16, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- The `LDLᵀ` certificate of `D16⁺`. -/
theorem energyD16_sos (z : Fin 16 → ℤ) :
    (energyD16 z : ℚ) =
      (2) * ((z 0 : ℚ) + (-1/2) * (z 1 : ℚ)) ^ 2 +
      (3/2) * ((z 1 : ℚ) + (-2/3) * (z 2 : ℚ)) ^ 2 +
      (4/3) * ((z 2 : ℚ) + (-3/4) * (z 3 : ℚ)) ^ 2 +
      (5/4) * ((z 3 : ℚ) + (-4/5) * (z 4 : ℚ)) ^ 2 +
      (6/5) * ((z 4 : ℚ) + (-5/6) * (z 5 : ℚ)) ^ 2 +
      (7/6) * ((z 5 : ℚ) + (-6/7) * (z 6 : ℚ)) ^ 2 +
      (8/7) * ((z 6 : ℚ) + (-7/8) * (z 7 : ℚ)) ^ 2 +
      (9/8) * ((z 7 : ℚ) + (-8/9) * (z 8 : ℚ)) ^ 2 +
      (10/9) * ((z 8 : ℚ) + (-9/10) * (z 9 : ℚ)) ^ 2 +
      (11/10) * ((z 9 : ℚ) + (-10/11) * (z 10 : ℚ)) ^ 2 +
      (12/11) * ((z 10 : ℚ) + (-11/12) * (z 11 : ℚ)) ^ 2 +
      (13/12) * ((z 11 : ℚ) + (-12/13) * (z 12 : ℚ)) ^ 2 +
      (14/13) * ((z 12 : ℚ) + (-13/14) * (z 13 : ℚ) + (-13/14) * (z 14 : ℚ)) ^ 2 +
      (15/14) * ((z 13 : ℚ) + (-13/15) * (z 14 : ℚ)) ^ 2 +
      (4/15) * ((z 14 : ℚ) + (15/4) * (z 15 : ℚ)) ^ 2 +
      (1/4) * ((z 15 : ℚ)) ^ 2 := by
  unfold energyD16
  push_cast
  ring

set_option maxHeartbeats 1000000 in
theorem d16plus_pos (z : Fin 16 → ℤ) (hz : z ≠ 0) : 0 < intEnergy d16plus z := by
  rw [intEnergy_d16plus]
  by_contra hle
  push Not at hle
  have hq : (energyD16 z : ℚ) ≤ 0 := by exact_mod_cast hle
  rw [energyD16_sos] at hq
  have s0 := sq_nonneg ((z 0 : ℚ) + (-1/2) * (z 1 : ℚ))
  have s1 := sq_nonneg ((z 1 : ℚ) + (-2/3) * (z 2 : ℚ))
  have s2 := sq_nonneg ((z 2 : ℚ) + (-3/4) * (z 3 : ℚ))
  have s3 := sq_nonneg ((z 3 : ℚ) + (-4/5) * (z 4 : ℚ))
  have s4 := sq_nonneg ((z 4 : ℚ) + (-5/6) * (z 5 : ℚ))
  have s5 := sq_nonneg ((z 5 : ℚ) + (-6/7) * (z 6 : ℚ))
  have s6 := sq_nonneg ((z 6 : ℚ) + (-7/8) * (z 7 : ℚ))
  have s7 := sq_nonneg ((z 7 : ℚ) + (-8/9) * (z 8 : ℚ))
  have s8 := sq_nonneg ((z 8 : ℚ) + (-9/10) * (z 9 : ℚ))
  have s9 := sq_nonneg ((z 9 : ℚ) + (-10/11) * (z 10 : ℚ))
  have s10 := sq_nonneg ((z 10 : ℚ) + (-11/12) * (z 11 : ℚ))
  have s11 := sq_nonneg ((z 11 : ℚ) + (-12/13) * (z 12 : ℚ))
  have s12 := sq_nonneg ((z 12 : ℚ) + (-13/14) * (z 13 : ℚ) + (-13/14) * (z 14 : ℚ))
  have s13 := sq_nonneg ((z 13 : ℚ) + (-13/15) * (z 14 : ℚ))
  have s14 := sq_nonneg ((z 14 : ℚ) + (15/4) * (z 15 : ℚ))
  have s15 := sq_nonneg ((z 15 : ℚ))
  generalize ha0 : ((z 0 : ℚ) + (-1/2) * (z 1 : ℚ)) ^ 2 = a0 at hq s0
  generalize ha1 : ((z 1 : ℚ) + (-2/3) * (z 2 : ℚ)) ^ 2 = a1 at hq s1
  generalize ha2 : ((z 2 : ℚ) + (-3/4) * (z 3 : ℚ)) ^ 2 = a2 at hq s2
  generalize ha3 : ((z 3 : ℚ) + (-4/5) * (z 4 : ℚ)) ^ 2 = a3 at hq s3
  generalize ha4 : ((z 4 : ℚ) + (-5/6) * (z 5 : ℚ)) ^ 2 = a4 at hq s4
  generalize ha5 : ((z 5 : ℚ) + (-6/7) * (z 6 : ℚ)) ^ 2 = a5 at hq s5
  generalize ha6 : ((z 6 : ℚ) + (-7/8) * (z 7 : ℚ)) ^ 2 = a6 at hq s6
  generalize ha7 : ((z 7 : ℚ) + (-8/9) * (z 8 : ℚ)) ^ 2 = a7 at hq s7
  generalize ha8 : ((z 8 : ℚ) + (-9/10) * (z 9 : ℚ)) ^ 2 = a8 at hq s8
  generalize ha9 : ((z 9 : ℚ) + (-10/11) * (z 10 : ℚ)) ^ 2 = a9 at hq s9
  generalize ha10 : ((z 10 : ℚ) + (-11/12) * (z 11 : ℚ)) ^ 2 = a10 at hq s10
  generalize ha11 : ((z 11 : ℚ) + (-12/13) * (z 12 : ℚ)) ^ 2 = a11 at hq s11
  generalize ha12 : ((z 12 : ℚ) + (-13/14) * (z 13 : ℚ) + (-13/14) * (z 14 : ℚ)) ^ 2 = a12 at hq s12
  generalize ha13 : ((z 13 : ℚ) + (-13/15) * (z 14 : ℚ)) ^ 2 = a13 at hq s13
  generalize ha14 : ((z 14 : ℚ) + (15/4) * (z 15 : ℚ)) ^ 2 = a14 at hq s14
  generalize ha15 : ((z 15 : ℚ)) ^ 2 = a15 at hq s15
  have l15 : (z 15 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha15.trans (by linarith))
  have l14 : (z 14 : ℚ) + (15/4) * (z 15 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha14.trans (by linarith))
  have l13 : (z 13 : ℚ) + (-13/15) * (z 14 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha13.trans (by linarith))
  have l12 : (z 12 : ℚ) + (-13/14) * (z 13 : ℚ) + (-13/14) * (z 14 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha12.trans (by linarith))
  have l11 : (z 11 : ℚ) + (-12/13) * (z 12 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha11.trans (by linarith))
  have l10 : (z 10 : ℚ) + (-11/12) * (z 11 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha10.trans (by linarith))
  have l9 : (z 9 : ℚ) + (-10/11) * (z 10 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha9.trans (by linarith))
  have l8 : (z 8 : ℚ) + (-9/10) * (z 9 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha8.trans (by linarith))
  have l7 : (z 7 : ℚ) + (-8/9) * (z 8 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha7.trans (by linarith))
  have l6 : (z 6 : ℚ) + (-7/8) * (z 7 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha6.trans (by linarith))
  have l5 : (z 5 : ℚ) + (-6/7) * (z 6 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha5.trans (by linarith))
  have l4 : (z 4 : ℚ) + (-5/6) * (z 5 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha4.trans (by linarith))
  have l3 : (z 3 : ℚ) + (-4/5) * (z 4 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha3.trans (by linarith))
  have l2 : (z 2 : ℚ) + (-3/4) * (z 3 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha2.trans (by linarith))
  have l1 : (z 1 : ℚ) + (-2/3) * (z 2 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha1.trans (by linarith))
  have l0 : (z 0 : ℚ) + (-1/2) * (z 1 : ℚ) = 0 :=
    (pow_eq_zero_iff (n := 2) two_ne_zero).mp (ha0.trans (by linarith))
  have q15 : (z 15 : ℚ) = 0 := by linarith only [l15]
  have q14 : (z 14 : ℚ) = 0 := by linarith only [l14, q15]
  have q13 : (z 13 : ℚ) = 0 := by linarith only [l13, q14, q15]
  have q12 : (z 12 : ℚ) = 0 := by linarith only [l12, q13, q14, q15]
  have q11 : (z 11 : ℚ) = 0 := by linarith only [l11, q12, q13, q14, q15]
  have q10 : (z 10 : ℚ) = 0 := by linarith only [l10, q11, q12, q13, q14, q15]
  have q9 : (z 9 : ℚ) = 0 := by linarith only [l9, q10, q11, q12, q13, q14, q15]
  have q8 : (z 8 : ℚ) = 0 := by linarith only [l8, q9, q10, q11, q12, q13, q14, q15]
  have q7 : (z 7 : ℚ) = 0 := by linarith only [l7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q6 : (z 6 : ℚ) = 0 := by linarith only [l6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q5 : (z 5 : ℚ) = 0 := by linarith only [l5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q4 : (z 4 : ℚ) = 0 := by linarith only [l4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q3 : (z 3 : ℚ) = 0 := by linarith only [l3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q2 : (z 2 : ℚ) = 0 := by linarith only [l2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q1 : (z 1 : ℚ) = 0 := by linarith only [l1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  have q0 : (z 0 : ℚ) = 0 := by linarith only [l0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  apply hz
  funext i
  have h : ∀ j, (z j : ℚ) = 0 := by
    intro j
    fin_cases j
    exacts [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15]
  exact_mod_cast h i


theorem d16plus_isSymm : d16plus.IsSymm := by decide

theorem e8sq_isSymm : e8sq.IsSymm := by decide

theorem e8sq_pos (z : Fin 16 → ℤ) (hz : z ≠ 0) : 0 < intEnergy e8sq z := by
  rw [intEnergy_e8sq]
  have hl := e8_evenPos.energy_nonneg (lft z)
  have hr := e8_evenPos.energy_nonneg (rgt z)
  by_cases hl0 : lft z = 0
  · have hr0 : rgt z ≠ 0 := fun h => hz (eq_of_lft_rgt (by rw [hl0]; rfl) (by rw [h]; rfl))
    have := e8_evenPos.pos _ hr0
    omega
  · have := e8_evenPos.pos _ hl0
    omega

/-- No class of `E8 ⊕ E8` holds 17 distinct energy-four sectors. -/
theorem e8sq_classTuples_isEmpty : IsEmpty (classTuples e8sq 4 17) := by
  classical
  refine ⟨fun ⟨X, hE, hinj, hc⟩ => ?_⟩
  have h := e8sq_class_card_le (Finset.univ.image X)
    (fun x hx => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact hE i)
    (fun x hx y hy l => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hc i j l)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at h
  omega

theorem d16frame_length : d16frame.length = 32 := rfl

theorem d16frame_nodup : d16frame.Nodup := by decide

/-- `D16⁺` has 17 distinct energy-four sectors in one class: the first
17 of the frame `±2eᵢ`. -/
theorem d16plus_classTuples_nonempty : Nonempty (classTuples d16plus 4 17) := by
  let X : Fin 17 → Fin 16 → ℤ := fun i =>
    d16frame.get (Fin.castLE (by rw [d16frame_length]; norm_num) i)
  refine ⟨⟨X, fun i => d16frame_energy _ (List.get_mem _ _), fun i j h => ?_,
    fun i j l => d16frame_cong _ (List.get_mem _ _) _ (List.get_mem _ _) l⟩⟩
  exact Fin.castLE_injective _ (d16frame_nodup.get_inj_iff.mp h)

/-- **`E8 ⊕ E8` and `D16⁺` have different representation numbers in
degree 17**: some `17 × 17` Gram matrix is represented by them in
non-equinumerous ways. -/
theorem e8sq_d16plus_siegel_ne :
    ∃ T : Matrix (Fin 17) (Fin 17) ℤ, IsEmpty (siegelSetK e8sq T ≃ siegelSetK d16plus T) := by
  by_contra h
  push Not at h
  have e := classTuplesEquivOfSiegel (k := 16) e8sq_isSymm d16plus_isSymm e8sq_pos d16plus_pos
    (fun T => h T) 4
  obtain ⟨X⟩ := d16plus_classTuples_nonempty
  exact e8sq_classTuples_isEmpty.false (e.symm X)

end Theaetetus
