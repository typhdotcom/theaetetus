-- ported from Meno/TowerGravity.lean (the scalar witness engine,
-- private there — republished here per the copy-map)
import Theaetetus.Defect
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The witness

The defect is strictly negative at the smallest incomparable pair:
`D_{1/3}(2, 3) < 0`, i.e. `θ(4/3)·θ(3) < θ(1/3)·θ(12)`
(`theta_crossRatio_lt`, the engine; `defect_witness`, the sign).

The scale `s = 1/3` is the witness's birthplace: it is the harmonic
energy `k²/3` of the cycle graph `C₃`, the smallest carrier of rank
one (PROGRAM.md, the seed). Here it is simply the first point of Q1.

The proof computes nothing transcendental: each theta value is
sandwiched by one explicit mode plus a geometric tail (`theta_ge`,
`theta_le`), the exponential bounds reduce to ninth-decimal bounds
on `e`, and the comparison closes by rational arithmetic —
`(127/73)·(21/19) < 12/5`. -/

namespace Theaetetus

/-- Bounds on `exp(1/3)` from the ninth-decimal bounds on `e`. -/
private lemma exp_third_bounds :
    (1.39 : ℝ) < Real.exp (1 / 3) ∧ Real.exp (1 / 3) < 10 / 7 := by
  have hcube : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hgt := Real.exp_one_gt_d9
  have hlt := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp (1 / 3) := Real.exp_pos _
  constructor
  · by_contra hle
    push_neg at hle
    have h3 : Real.exp (1 / 3) ^ 3 ≤ (1.39 : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ hpos.le hle 3
    rw [hcube] at h3
    norm_num at h3
    linarith
  · by_contra hge
    push_neg at hge
    have h3 : (10 / 7 : ℝ) ^ 3 ≤ Real.exp (1 / 3) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) hge 3
    rw [hcube] at h3
    norm_num at h3
    linarith

/-- The three numeric exponential bounds the strictness consumes. -/
theorem exp_numeric_bounds :
    (7 / 10 : ℝ) < Real.exp (-(1 / 3))
      ∧ Real.exp (-(4 / 3)) < 27 / 100
      ∧ Real.exp (-3) < 1 / 20 := by
  obtain ⟨hy1, hy2⟩ := exp_third_bounds
  have hpos : (0 : ℝ) < Real.exp (1 / 3) := Real.exp_pos _
  have hcube : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hgt := Real.exp_one_gt_d9
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.exp_neg]
    calc (7 / 10 : ℝ) = (10 / 7 : ℝ)⁻¹ := by norm_num
      _ < (Real.exp (1 / 3))⁻¹ := by
          exact inv_strictAnti₀ hpos hy2
  · have h4 : Real.exp (-(4 / 3)) = (Real.exp (1 / 3) ^ 4)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      norm_num
    rw [h4]
    have hy4 : (100 / 27 : ℝ) < Real.exp (1 / 3) ^ 4 := by
      have : Real.exp (1 / 3) ^ 4 = Real.exp (1 / 3) * Real.exp 1 := by
        rw [← hcube]
        ring
      rw [this]
      nlinarith
    calc (Real.exp (1 / 3) ^ 4)⁻¹ < (100 / 27 : ℝ)⁻¹ := by
          exact inv_strictAnti₀ (by norm_num) hy4
      _ = 27 / 100 := by norm_num
  · have h3 : Real.exp (-3) = (Real.exp 1 ^ 3)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      norm_num
    rw [h3]
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hgt)
        (by positivity : (0 : ℝ) < Real.exp 1 + 2.7182818283)]
    have he3 : (20 : ℝ) < Real.exp 1 ^ 3 := by
      nlinarith [mul_pos (sub_pos.mpr hgt)
        (by positivity : (0 : ℝ) < Real.exp 1 ^ 2), h2, hgt, he_pos]
    calc (Real.exp 1 ^ 3)⁻¹ < (20 : ℝ)⁻¹ := by
          exact inv_strictAnti₀ (by norm_num) he3
      _ = 1 / 20 := by norm_num

/-- **The theta-value comparison** (the witness engine):
`θ(4/3)·θ(3) < θ(1/3)·θ(12)` — partial sums against geometric
tails, closed by rational arithmetic. -/
theorem theta_crossRatio_lt :
    theta (4 / 3) * theta 3 < theta (1 / 3) * theta 12 := by
  obtain ⟨hc, ha, hb⟩ := exp_numeric_bounds
  have ha_pos : (0 : ℝ) < Real.exp (-(4 / 3)) := Real.exp_pos _
  have hb_pos : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
  have h43 : theta (4 / 3) < 127 / 73 := by
    have hle := theta_le (4 / 3) (by norm_num)
    have hfrac : Real.exp (-(4 / 3)) / (1 - Real.exp (-(4 / 3))) < 27 / 73 := by
      rw [div_lt_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have h3 : theta 3 < 21 / 19 := by
    have hle := theta_le 3 (by norm_num)
    have hfrac : Real.exp (-3) / (1 - Real.exp (-3)) < 1 / 19 := by
      rw [div_lt_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have h13 : (12 / 5 : ℝ) < theta (1 / 3) := by
    have hge := theta_ge (1 / 3) (by norm_num)
    nlinarith
  have h12 : (1 : ℝ) ≤ theta 12 :=
    (theta_gt_one 12 (by norm_num)).le
  have h43_pos : (0 : ℝ) < theta (4 / 3) := theta_pos (4 / 3) (by norm_num)
  have h3_pos : (0 : ℝ) < theta 3 := theta_pos 3 (by norm_num)
  calc theta (4 / 3) * theta 3
      < (127 / 73) * (21 / 19) := by
        exact mul_lt_mul'' h43 h3 h43_pos.le h3_pos.le
    _ < 12 / 5 := by norm_num
    _ < theta (1 / 3) := h13
    _ ≤ theta (1 / 3) * theta 12 := by
        nlinarith [h13]

/-- **THE WITNESS**: the defect is strictly negative at the smallest
incomparable pair — `D_{1/3}(2, 3) < 0`. The defect vanishes on
chains (`defect_eq_zero_of_dvd`) and strictly fails off them: `h` is
strictly supermodular at the witness, residue complexity strictly
submodular — the primes couple through the geometry, and the
coupling has a sign. -/
theorem defect_witness : defect (1 / 3) 2 3 < 0 := by
  unfold defect
  rw [show Nat.gcd 2 3 = 1 from by decide,
    show Nat.lcm 2 3 = 6 from by decide,
    show (((2 : ℕ) : ℝ)) ^ 2 * (1 / 3) = 4 / 3 from by norm_num,
    show (((3 : ℕ) : ℝ)) ^ 2 * (1 / 3) = 3 from by norm_num,
    show (((1 : ℕ) : ℝ)) ^ 2 * (1 / 3) = 1 / 3 from by norm_num,
    show (((6 : ℕ) : ℝ)) ^ 2 * (1 / 3) = 12 from by norm_num]
  have hkey := theta_crossRatio_lt
  have hp1 : (0 : ℝ) < theta (4 / 3) := theta_pos (4 / 3) (by norm_num)
  have hp2 : (0 : ℝ) < theta 3 := theta_pos 3 (by norm_num)
  have hp3 : (0 : ℝ) < theta (1 / 3) := theta_pos (1 / 3) (by norm_num)
  have hp4 : (0 : ℝ) < theta 12 := theta_pos 12 (by norm_num)
  have hlog := Real.log_lt_log (mul_pos hp1 hp2) hkey
  rw [Real.log_mul hp1.ne' hp2.ne', Real.log_mul hp3.ne' hp4.ne'] at hlog
  linarith

end Theaetetus
