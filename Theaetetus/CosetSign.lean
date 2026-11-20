import Theaetetus.CosetDuality
import Theaetetus.ThetaBounds

/-! # The classwise defect has no sign

The scalar defect is nonpositive at every scale (`gramDefect_nonpos`);
the classwise defect is not. At rank one with unit Gram, the odd
class `1 + 2ℤ` has mass `oddMass β = ∑_k e^{−β(2k+1)²}`
(`cosetMass_one_one`), squeezed between its two ground states and a
geometric tail: `2e^{−β} ≤ oddMass β ≤ 4e^{−β}` for `β ≥ 1`
(`two_exp_le_oddMass`, `oddMass_le_four_exp`). The class has no
zero-energy sector, so at large scale its defect grows with the
energy gap instead of decaying: at `s = 1` and resolutions `(2, 3)`
it is strictly positive (`cosetDefect_odd_pos`). -/

namespace Theaetetus

/-- The Boltzmann mass of the odd integers. -/
noncomputable def oddMass (β : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-(β * (2 * (k : ℝ) + 1) ^ 2))

theorem summable_oddMass {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : ℤ => Real.exp (-(β * (2 * (k : ℝ) + 1) ^ 2))) := by
  refine (summable_exp_shift (4 * β) (by positivity) (1 / 2)).congr fun k => ?_
  congr 2
  ring

/-- The rank-one odd coset mass is the odd mass. -/
theorem cosetMass_one_one (β : ℝ) :
    cosetMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ![1] β = oddMass β := by
  unfold cosetMass oddMass
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  refine tsum_congr fun k => ?_
  simp [dotProduct, Matrix.mulVec]
  ring_nf
  all_goals simp

/-- The odd mass folds onto the positive odd integers. -/
theorem oddMass_eq_two_mul {β : ℝ} (hβ : 0 < β) :
    oddMass β = 2 * ∑' n : ℕ, Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2)) := by
  have hs := summable_oddMass hβ
  have hpos : Summable (fun n : ℕ => Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2))) := by
    exact (hs.comp_injective Nat.cast_injective).congr fun n => by simp
  unfold oddMass
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ =>
      Real.exp (-(β * (2 * (k : ℝ) + 1) ^ 2))) (by simpa using hpos)]
  · have hneg : ∀ n : ℕ, Real.exp (-(β * (2 * ((-(n + 1 : ℤ) : ℤ) : ℝ) + 1) ^ 2))
        = Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2)) := fun n => by
      push_cast; ring_nf
    simp only [Int.cast_natCast, hneg]
    ring
  · refine (hpos.congr fun n => ?_)
    push_cast; ring_nf

theorem summable_oddMass_nat {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℕ => Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2))) := by
  exact ((summable_oddMass hβ).comp_injective Nat.cast_injective).congr fun n => by simp

/-- The two ground states bound the odd mass below. -/
theorem two_exp_le_oddMass {β : ℝ} (hβ : 0 < β) :
    2 * Real.exp (-β) ≤ oddMass β := by
  rw [oddMass_eq_two_mul hβ]
  have hs := summable_oddMass_nat hβ
  have h0 := hs.le_tsum 0 (fun n _ => (Real.exp_pos _).le)
  have : Real.exp (-(β * (2 * ((0 : ℕ) : ℝ) + 1) ^ 2)) = Real.exp (-β) := by
    norm_num
  linarith

/-- A geometric tail bounds the odd mass above, from `β ≥ 1`. -/
theorem oddMass_le_four_exp {β : ℝ} (hβ : 1 ≤ β) :
    oddMass β ≤ 4 * Real.exp (-β) := by
  have hβ0 : 0 < β := by linarith
  rw [oddMass_eq_two_mul hβ0]
  set r := Real.exp (-(8 * β)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    have : r ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith [exp_neg_one_lt]
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hterm : ∀ n : ℕ, Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2))
      ≤ Real.exp (-β) * (1 / 2 : ℝ) ^ n := by
    intro n
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      rcases n with _ | m
      · simp
      · push_cast
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    calc Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2))
        ≤ Real.exp (-β) * r ^ n := by
          rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [mul_nonneg hβ0.le hnn]
      _ ≤ Real.exp (-β) * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr1 n) (Real.exp_pos _).le
  have hsum : ∑' n : ℕ, Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2)) ≤ 2 * Real.exp (-β) := by
    calc ∑' n : ℕ, Real.exp (-(β * (2 * (n : ℝ) + 1) ^ 2))
        ≤ ∑' n : ℕ, Real.exp (-β) * (1 / 2 : ℝ) ^ n :=
          (summable_oddMass_nat hβ0).tsum_le_tsum hterm (hgeo.mul_left _)
      _ = Real.exp (-β) * 2 := by
          rw [hgeo.tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
      _ = 2 * Real.exp (-β) := by ring
  linarith

theorem oddMass_pos {β : ℝ} (hβ : 0 < β) : 0 < oddMass β :=
  lt_of_lt_of_le (by positivity) (two_exp_le_oddMass hβ)

/-- **The classwise defect has no sign**: the odd class of `ℤ ⧸ 2ℤ`
has strictly positive defect at `s = 1`, resolutions `(2, 3)`. -/
theorem cosetDefect_odd_pos :
    0 < fieldDefect (cosetMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ![1]) 1 2 3 := by
  have hZ : cosetMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ![1] = oddMass :=
    funext cosetMass_one_one
  rw [hZ, fieldDefect, show Nat.gcd 2 3 = 1 from by decide,
    show Nat.lcm 2 3 = 6 from by decide]
  norm_num
  have h4 := two_exp_le_oddMass (β := 4) (by norm_num)
  have h9 := two_exp_le_oddMass (β := 9) (by norm_num)
  have h1 := oddMass_le_four_exp (β := 1) le_rfl
  have h36 := oddMass_le_four_exp (β := 36) (by norm_num)
  have p1 := oddMass_pos (β := 1) one_pos
  have p4 := oddMass_pos (β := 4) (by norm_num)
  have p9 := oddMass_pos (β := 9) (by norm_num)
  have p36 := oddMass_pos (β := 36) (by norm_num)
  have hlow : 4 * Real.exp (-13) ≤ oddMass 4 * oddMass 9 := by
    have : 4 * Real.exp (-13) = (2 * Real.exp (-4)) * (2 * Real.exp (-9)) := by
      rw [show (-13 : ℝ) = -4 + -9 by norm_num, Real.exp_add]; ring
    rw [this]
    exact mul_le_mul h4 h9 (by positivity) p4.le
  have hup : oddMass 1 * oddMass 36 ≤ 16 * Real.exp (-37) := by
    have : 16 * Real.exp (-37) = (4 * Real.exp (-1)) * (4 * Real.exp (-36)) := by
      rw [show (-37 : ℝ) = -1 + -36 by norm_num, Real.exp_add]; ring
    rw [this]
    exact mul_le_mul h1 h36 p36.le (by positivity)
  have hgap : 16 * Real.exp (-37) < 4 * Real.exp (-13) := by
    have he : (25 : ℝ) ≤ Real.exp 24 := by
      have := Real.add_one_le_exp (24 : ℝ); linarith
    have : Real.exp (-13) = Real.exp 24 * Real.exp (-37) := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos (-37)]
  have hlt : Real.log (oddMass 1 * oddMass 36) < Real.log (oddMass 4 * oddMass 9) :=
    Real.log_lt_log (by positivity) (by linarith)
  rw [Real.log_mul p1.ne' p36.ne', Real.log_mul p4.ne' p9.ne'] at hlt
  linarith

end Theaetetus
