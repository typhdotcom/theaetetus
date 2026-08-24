import Theaetetus.ReflectionFourier

/-! # The strict maximum of the shifted Gaussian mass

Every Fourier coefficient of the shifted mass is strictly positive
(`massFourierCoeff_pos`), and a function with strictly positive
coefficients is pinned by that positivity: against the expansion at
the origin, where every character contributes its full weight, any
other shift loses `1 - cos` of each one. So the mass is maximal on
the lattice and strictly submaximal off it —

    gramMass M α x ≤ gramMass M α 0,  with equality iff x ∈ ℤᵈ

(`gramMass_le_gramMass_zero`, `gramMass_lt_gramMass_zero`,
`gramMass_eq_gramMass_zero_iff`). This is a rigidity statement about
the mass itself, not about a symmetry of the form: it says the
Gaussian mass has no accidental maximizer at any positive coupling
and in any rank. The parity feature vectors inherit it entrywise
(`parityVector_le_max`, `parityVector_eq_max_iff`).

The same theorems settle what the principle can do on its own
against the two-grid criterion. The criterion equates the mass at two
shifts differing by the displacement `residueShift a c`. Both can be
maximal only if that displacement is itself a lattice shift
(`isLatticeShift_of_add_of_sub`), and a residue shift is a lattice
shift only at the zero class — for every positive modulus, no
coprimality needed (`isLatticeShift_residueShift_iff`) — where the
criterion is an identity anyway (`parityVector_zero_displacement`).
So under the criterion every nonzero-displacement pair sits strictly
below the maximum on both sides (`twoGridReflection_lt_max`), and the
equality it asserts is between two strictly submaximal values. The
maximum principle alone therefore cannot contradict the criterion.
That is a statement about the principle used by itself; it leaves
open what it contributes alongside a second comparison. -/

namespace Theaetetus

open Finset

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## Lattice shifts -/

/-- A shift is a lattice point when every coordinate is an integer.
The mass is `ℤᵈ`-periodic, so these are exactly the shifts it cannot
distinguish from the origin. -/
def IsLatticeShift (x : Fin d → ℝ) : Prop :=
  ∃ k : Fin d → ℤ, x = fun i => (k i : ℝ)

theorem isLatticeShift_zero : IsLatticeShift (0 : Fin d → ℝ) :=
  ⟨0, by funext i; simp⟩

/-- A shift is a lattice point exactly when each coordinate is. -/
theorem isLatticeShift_iff_forall {x : Fin d → ℝ} :
    IsLatticeShift x ↔ ∀ i, ∃ k : ℤ, x i = (k : ℝ) := by
  constructor
  · rintro ⟨k, rfl⟩ i
    exact ⟨k i, rfl⟩
  · intro h
    choose k hk using h
    exact ⟨k, funext hk⟩

theorem gramMass_of_isLatticeShift (α : ℝ) {x : Fin d → ℝ}
    (hx : IsLatticeShift x) : gramMass M α x = gramMass M α 0 := by
  obtain ⟨k, rfl⟩ := hx
  have h := gramMass_int_shift (M := M) α 0 k
  simpa using h

/-! ## The Fourier gap -/

/-- The gap to the origin, resolved character by character: each dual
vector contributes its positive weight times `1 - cos`. -/
private theorem hasSum_massGap (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        massFourierCoeff M α m
          * (1 - Real.cos (2 * Real.pi * dualPairing m x)))
      (gramMass M α 0 - gramMass M α x) := by
  have h := (hasSum_massFourier_cos hM hα 0).sub
    (hasSum_massFourier_cos hM hα x)
  refine h.congr_fun fun m => ?_
  have hz : dualPairing m (0 : Fin d → ℝ) = 0 := by
    simp [dualPairing]
  rw [hz, mul_zero, Real.cos_zero]
  ring

private theorem massGap_nonneg (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (m : Fin d → ℤ) :
    0 ≤ massFourierCoeff M α m
      * (1 - Real.cos (2 * Real.pi * dualPairing m x)) :=
  mul_nonneg (massFourierCoeff_pos hM hα m).le
    (sub_nonneg.mpr (Real.cos_le_one _))

/-! ## The maximum principle -/

/-- **The maximum principle**: the shifted Gaussian mass is largest
at the lattice. -/
theorem gramMass_le_gramMass_zero (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) : gramMass M α x ≤ gramMass M α 0 := by
  have h := hasSum_le (fun m => massGap_nonneg hM hα x m) hasSum_zero
    (hasSum_massGap hM hα x)
  linarith

/-- The pairing of a shift with a single dual basis vector reads off
one coordinate. -/
private theorem dualPairing_single (i₀ : Fin d) (x : Fin d → ℝ) :
    dualPairing (fun i => if i = i₀ then (1 : ℤ) else 0) x = x i₀ := by
  rw [dualPairing, Finset.sum_eq_single i₀] <;> simp +contextual

private theorem cos_ne_one_of_not_int {t : ℝ} (h : ∀ k : ℤ, t ≠ (k : ℝ)) :
    Real.cos (2 * Real.pi * t) ≠ 1 := by
  intro hc
  rw [Real.cos_eq_one_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  exact h n (mul_left_cancel₀ h2 (by linear_combination -hn))

/-- **Strictness off the lattice**: at any positive coupling and in
any rank, a shift that is not a lattice point carries strictly less
mass than the origin. The Gaussian mass has no accidental
maximizer. -/
theorem gramMass_lt_gramMass_zero (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    {x : Fin d → ℝ} (hx : ¬ IsLatticeShift x) :
    gramMass M α x < gramMass M α 0 := by
  have hcoord : ∃ i₀ : Fin d, ∀ k : ℤ, x i₀ ≠ (k : ℝ) := by
    by_contra hall
    refine hx ?_
    simp only [not_exists, not_forall, not_ne_iff] at hall
    choose k hk using hall
    exact ⟨k, funext hk⟩
  obtain ⟨i₀, hi₀⟩ := hcoord
  set m₀ : Fin d → ℤ := fun i => if i = i₀ then (1 : ℤ) else 0 with hm₀
  have hstrict : 0 < massFourierCoeff M α m₀
      * (1 - Real.cos (2 * Real.pi * dualPairing m₀ x)) := by
    refine mul_pos (massFourierCoeff_pos hM hα m₀) ?_
    rw [hm₀, dualPairing_single]
    have hne := cos_ne_one_of_not_int hi₀
    have hle := Real.cos_le_one (2 * Real.pi * x i₀)
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  have h := hasSum_lt (fun m => massGap_nonneg hM hα x m) hstrict
    hasSum_zero (hasSum_massGap hM hα x)
  linarith

/-- **The equality case**: the mass matches the origin exactly on the
lattice. -/
theorem gramMass_eq_gramMass_zero_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    gramMass M α x = gramMass M α 0 ↔ IsLatticeShift x := by
  refine ⟨fun h => ?_, gramMass_of_isLatticeShift α⟩
  by_contra hx
  exact absurd h (gramMass_lt_gramMass_zero hM hα hx).ne

/-! ## The parity feature vectors -/

theorem parityVector_zero_zero (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) :
    parityVector M α 0 0 = gramMass M (2 * α) 0 := by
  refine congrArg (gramMass M (2 * α)) ?_
  funext i
  show (2 : ℝ)⁻¹ * ((0 : Fin d → ℝ) i + (((0 : Fin d → ZMod 2) i).val : ℝ))
    = (0 : Fin d → ℝ) i
  simp

/-- Every entry of a parity feature vector is bounded by the mass at
the origin. -/
theorem parityVector_le_max (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (z : Fin d → ℝ) (c : Fin d → ZMod 2) :
    parityVector M α z c ≤ gramMass M (2 * α) 0 :=
  gramMass_le_gramMass_zero hM (by linarith) _

/-- An entry attains that bound exactly at a lattice shift. -/
theorem parityVector_eq_max_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (z : Fin d → ℝ) (c : Fin d → ZMod 2) :
    parityVector M α z c = gramMass M (2 * α) 0
      ↔ IsLatticeShift ((2 : ℝ)⁻¹ • (z + fun i => ((c i).val : ℝ))) :=
  gramMass_eq_gramMass_zero_iff hM (by linarith) _

/-! ## The reach of the principle on the two-grid criterion -/

/-- Two half-shifts that are both lattice points force their
displacement to be a lattice shift. -/
theorem isLatticeShift_of_add_of_sub {u v : Fin d → ℝ}
    (hp : IsLatticeShift ((2 : ℝ)⁻¹ • (u + v)))
    (hm : IsLatticeShift ((2 : ℝ)⁻¹ • (u - v))) : IsLatticeShift v := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨m, hm⟩ := hm
  refine ⟨p - m, funext fun i => ?_⟩
  have hpi := congrFun hp i
  have hmi := congrFun hm i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul] at hpi hmi
  show v i = (((p - m) i : ℤ) : ℝ)
  simp only [Pi.sub_apply]
  push_cast
  linarith

/-- A residue shift is a lattice point only at the zero class: the
representatives are the least nonnegative ones. -/
theorem isLatticeShift_residueShift_iff {n : ℕ} (hn : 0 < n)
    (c : Fin d → ZMod n) : IsLatticeShift (residueShift n c) ↔ c = 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  constructor
  · rintro ⟨k, hk⟩
    funext i
    have hki := congrFun hk i
    show c i = 0
    have hval : (((c i).val : ℕ) : ℝ) = (n : ℝ) * (k i : ℝ) := by
      have : (n : ℝ)⁻¹ * (((c i).val : ℕ) : ℝ) = (k i : ℝ) := hki
      field_simp at this
      linarith
    have hnat : ((c i).val : ℤ) = (n : ℤ) * k i := by exact_mod_cast hval
    have hlt : ((c i).val : ℤ) < (n : ℤ) := by
      exact_mod_cast ZMod.val_lt (c i)
    have hge : (0 : ℤ) ≤ (n : ℤ) * k i := by
      rw [← hnat]; positivity
    have hup : (n : ℤ) * k i < (n : ℤ) := by rw [← hnat]; exact hlt
    have hk0 : k i = 0 := by
      have h1 : (0 : ℤ) ≤ k i := by nlinarith
      have h2 : k i < 1 := by nlinarith
      omega
    have hv0 : (c i).val = 0 := by
      have := hnat
      rw [hk0, mul_zero] at this
      exact_mod_cast this
    have hcast : (((c i).val : ℕ) : ZMod n) = c i := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [← hcast, hv0]
    simp
  · rintro rfl
    refine ⟨0, funext fun i => ?_⟩
    show (n : ℝ)⁻¹ * ((((0 : Fin d → ZMod n) i).val : ℕ) : ℝ) = ((0 : ℤ) : ℝ)
    simp

/-- At the zero displacement class the criterion is an identity: the
two reflected shifts coincide. All of its content lies at nonzero
classes. -/
theorem residueShift_zero (n : ℕ) :
    residueShift n (0 : Fin d → ZMod n) = (0 : Fin d → ℝ) := by
  funext i
  show (n : ℝ)⁻¹ * ((((0 : Fin d → ZMod n) i).val : ℕ) : ℝ) = 0
  simp

theorem parityVector_zero_displacement (M : Matrix (Fin d) (Fin d) ℝ)
    (β : ℝ) {a : ℕ} (z : Fin d → ℝ) :
    parityVector M β (z + residueShift a (0 : Fin d → ZMod a))
      = parityVector M β (z - residueShift a (0 : Fin d → ZMod a)) := by
  rw [residueShift_zero, add_zero, sub_zero]

/-- **What the maximum principle settles on its own**: under the
two-grid criterion every reflected pair with a nonzero displacement
sits strictly below the maximum on *both* sides. Both sides maximal
would make the displacement a lattice shift, which at a residue class
means the zero class. The equality the criterion asserts is therefore
always between two strictly submaximal masses, so the maximum
principle by itself cannot contradict the criterion. -/
theorem twoGridReflection_lt_max (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : TwoGridReflection M s a b) {r : Fin d → ZMod b}
    {c : Fin d → ZMod a} (hc : c ≠ 0) (e : Fin d → ZMod 2) :
    parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
          (residueShift b r + residueShift a c) e
        < gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0
      ∧ parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
          (residueShift b r - residueShift a c) e
        < gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hβ : (0 : ℝ) < (a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s) := by positivity
  have hsides := congrFun (h r c) e
  have hplus : parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
      (residueShift b r + residueShift a c) e
      < gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0 := by
    refine lt_of_le_of_ne (parityVector_le_max hM hβ _ e) fun hmax => ?_
    have hmin : parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
        (residueShift b r - residueShift a c) e
        = gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0 := by
      rw [← hsides, hmax]
    have hp := (parityVector_eq_max_iff hM hβ _ e).mp hmax
    have hm := (parityVector_eq_max_iff hM hβ _ e).mp hmin
    refine hc ((isLatticeShift_residueShift_iff ha c).mp ?_)
    refine isLatticeShift_of_add_of_sub (u := residueShift b r
      + fun i => (((e i).val : ℕ) : ℝ)) (v := residueShift a c) ?_ ?_
    · refine hp.imp fun k hk => ?_
      rw [← hk]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    · refine hm.imp fun k hk => ?_
      rw [← hk]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      ring
  exact ⟨hplus, hsides ▸ hplus⟩

end Theaetetus
