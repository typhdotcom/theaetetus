import Theaetetus.Theta
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Bounds for θ: numeric exponentials and structural estimates

Rational bounds on `exp (-1)`, `exp (-2)`, `exp (-4)` from the
ninth-decimal bounds on `e` (the inversion/power trick of the
witness), antitonicity of `θ` in the coupling, a two-mode upper
bound sharper than the one-mode `theta_le`, and summability of
center-shifted Gaussian sums over `ℤ`. -/

namespace Theaetetus

/-! ## Numeric exponential bounds -/

/-- 1. `e⁻¹ < 37/100`, from the ninth-decimal lower bound on `e`:
`e > 2.718281828 > 100/37`. -/
theorem exp_neg_one_lt : Real.exp (-1) < 37 / 100 := by
  have h : (100 / 37 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  rw [Real.exp_neg]
  calc (Real.exp 1)⁻¹ < ((100 : ℝ) / 37)⁻¹ := inv_strictAnti₀ (by norm_num) h
    _ = 37 / 100 := by norm_num

/-- 2. `9/25 < e⁻¹`, from the ninth-decimal upper bound on `e`:
`e < 2.718281829 < 25/9`. -/
theorem exp_neg_one_gt : (9 : ℝ) / 25 < Real.exp (-1) := by
  have h : Real.exp 1 < 25 / 9 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.exp_neg]
  calc (9 : ℝ) / 25 = ((25 : ℝ) / 9)⁻¹ := by norm_num
    _ < (Real.exp 1)⁻¹ := inv_strictAnti₀ (Real.exp_pos 1) h

/-- 3. `e⁻² < 1369/10000`: the square of bound 1. -/
theorem exp_neg_two_lt : Real.exp (-2) < 1369 / 10000 := by
  have hsq : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [hsq]
  nlinarith [exp_neg_one_lt, Real.exp_pos (-1)]

/-- 4. `e⁻⁴ < 1874161/100000000`: the square of bound 3
(`37⁴ = 1874161`). -/
theorem exp_neg_four_lt : Real.exp (-4) < 1874161 / 100000000 := by
  have hsq : Real.exp (-4) = Real.exp (-2) * Real.exp (-2) := by
    rw [← Real.exp_add]; norm_num
  rw [hsq]
  nlinarith [exp_neg_two_lt, Real.exp_pos (-2)]

/-! ## Structural estimates -/

/-- 5. Antitonicity in the coupling: a larger coupling damps every
mode, so `θ(β) ≤ θ(α)` whenever `α ≤ β`. -/
theorem theta_anti {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) : theta β ≤ theta α := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  unfold theta
  refine (summable_theta β hβ).tsum_le_tsum (fun k => ?_) (summable_theta α hα)
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_nonneg ((k : ℝ))]

/-- 6. Two-mode upper bound: the vacuum term, twice the first mode,
and a geometric tail dominated by `e^{-4α}/(1 − e^{-2α})` — for
`k ≥ 1` one has `(k+1)² ≥ 2(k+1)`, so the tail of the positive-mode
sum is a geometric series in `e^{-2α}` starting at `e^{-4α}`. -/
theorem theta_le_two_mode {α : ℝ} (hα : 0 < α) :
    theta α ≤ 1 + 2 * Real.exp (-α)
      + 2 * (Real.exp (-(4 * α)) / (1 - Real.exp (-(2 * α)))) := by
  have hsub := theta_sub_one_eq α hα
  have hshift := summable_exp_sq_shift α hα
  have hr_pos : (0 : ℝ) < Real.exp (-(2 * α)) := Real.exp_pos _
  have hr_lt : Real.exp (-(2 * α)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeo : Summable (fun k : ℕ => Real.exp (-(2 * α)) ^ k) :=
    summable_geometric_of_lt_one hr_pos.le hr_lt
  have htail_sum :
      Summable (fun k : ℕ => Real.exp (-α * (((k + 1 : ℕ) : ℝ) + 1) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hshift
  have hterm : ∀ k : ℕ, Real.exp (-α * (((k + 1 : ℕ) : ℝ) + 1) ^ 2)
      ≤ Real.exp (-(4 * α)) * Real.exp (-(2 * α)) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    nlinarith [mul_nonneg hα.le hk, mul_nonneg (mul_nonneg hα.le hk) hk]
  have hsplit : ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      = Real.exp (-α * (((0 : ℕ) : ℝ) + 1) ^ 2)
        + ∑' k : ℕ, Real.exp (-α * (((k + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    hshift.tsum_eq_zero_add
  have h0 : Real.exp (-α * (((0 : ℕ) : ℝ) + 1) ^ 2) = Real.exp (-α) := by
    norm_num
  have htail : ∑' k : ℕ, Real.exp (-α * (((k + 1 : ℕ) : ℝ) + 1) ^ 2)
      ≤ Real.exp (-(4 * α)) / (1 - Real.exp (-(2 * α))) := by
    calc ∑' k : ℕ, Real.exp (-α * (((k + 1 : ℕ) : ℝ) + 1) ^ 2)
        ≤ ∑' k : ℕ, Real.exp (-(4 * α)) * Real.exp (-(2 * α)) ^ k :=
          htail_sum.tsum_le_tsum hterm (hgeo.mul_left _)
      _ = Real.exp (-(4 * α)) * ∑' k : ℕ, Real.exp (-(2 * α)) ^ k :=
          hgeo.tsum_mul_left _
      _ = Real.exp (-(4 * α)) * (1 - Real.exp (-(2 * α)))⁻¹ := by
          rw [tsum_geometric_of_lt_one hr_pos.le hr_lt]
      _ = Real.exp (-(4 * α)) / (1 - Real.exp (-(2 * α))) := by
          rw [div_eq_mul_inv]
  rw [h0] at hsplit
  linarith

/-- 7. Center-shifted summability: `∑ exp(−α(k+c)²)` converges for
any shift `c`, by domination against `θ(α/2)` scaled by `e^{αc²}` —
the cross term is absorbed via `(k+c)² ≥ k²/2 − c²`, i.e.
`0 ≤ (k+2c)²`. -/
theorem summable_exp_shift (α : ℝ) (hα : 0 < α) (c : ℝ) :
    Summable (fun k : ℤ => Real.exp (-(α * ((k : ℝ) + c) ^ 2))) := by
  have hhalf : (0 : ℝ) < α / 2 := by positivity
  have hdom : Summable
      (fun k : ℤ => Real.exp (α * c ^ 2) * Real.exp (-(α / 2) * (k : ℝ) ^ 2)) :=
    (summable_theta (α / 2) hhalf).mul_left _
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hdom
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_nonneg hα.le (sq_nonneg ((k : ℝ) + 2 * c))]

end Theaetetus
