import Theaetetus.Defect
import Theaetetus.Duality
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The sign at (2, 3): the birth certificate

**`D_s(2,3) < 0` for every `s > 0`** (`defect_two_three_neg`) — the
first native theorem: at the smallest incomparable pair the defect
is strictly negative at every scale. Q1's first infinite family.

In theta values: `θ(4s)·θ(9s) < θ(s)·θ(36s)`. Expanded over ℤ² this
compares the forms `4m²+9n²` and `m²+36n²`, which are **not**
termwise comparable (13 is represented by the first and not the
second) — the inequality is irreducibly aggregate.

The proof:

* **Duality is an involution on the problem**
  (`theta_prod_lt` branch two): the `gcd·lcm = q·q′` identity
  `4·9 = 1·36` makes the four Jacobi prefactors cancel between the
  sides, so the statement at `s` is equivalent to the statement at
  `s′ = π²/(36s)` — consumed as `theta_rect_lt_iff` at `(2, 3)`.
* **Large scales close geometrically**
  (`theta_prod_lt_of_half_le`): for `s ≥ 1/2`, with
  `q := e^(−s) ≤ 61/100`, geometric tails give
  `θ(4s)·θ(9s) ≤ (1 + cq⁴)(1 + cq⁹) < 1 + 2q ≤ θ(s) < θ(s)·θ(36s)`
  — the single first mode of `θ(s)` beats everything the left
  side has.
* The regimes overlap because `π > 3`:
  `s < 1/2 → π²/(36s) > π²/18 > 1/2`. -/

namespace Theaetetus

/-- **The large-scale branch**: for `s ≥ 1/2` the cross-ratio
comparison `θ(4s)·θ(9s) < θ(s)·θ(36s)` follows from geometric tail
bounds — the first mode `2e^(−s)` of `θ(s)` dominates the entire
excess of the left-hand side. -/
theorem theta_prod_lt_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) :
    theta (4 * s) * theta (9 * s) < theta s * theta (36 * s) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
  -- the modulus `q = e^(−s)` is at most 61/100, since `e > (100/61)²`
  have hq_half : Real.exp (-s) ≤ Real.exp (-(1 / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hhalf_lt : Real.exp (-(1 / 2)) < 61 / 100 := by
    rw [Real.exp_neg]
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hgt : (100 / 61 : ℝ) < Real.exp (1 / 2) := by
      by_contra hle
      push_neg at hle
      have h2 : Real.exp (1 / 2) ^ 2 ≤ (100 / 61 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hle 2
      rw [hsq] at h2
      norm_num at h2
      linarith [Real.exp_one_gt_d9]
    calc (Real.exp (1 / 2))⁻¹ < (100 / 61 : ℝ)⁻¹ :=
          inv_strictAnti₀ (by norm_num) hgt
      _ = 61 / 100 := by norm_num
  set q : ℝ := Real.exp (-s) with hq
  have hq0 : 0 < q := by rw [hq]; exact Real.exp_pos _
  have hqle : q ≤ 61 / 100 := hq_half.trans hhalf_lt.le
  -- powers of the modulus
  have hq3 : q ^ 3 ≤ (61 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ hq0.le hqle 3
  have hq8 : q ^ 8 ≤ (61 / 100 : ℝ) ^ 8 := pow_le_pow_left₀ hq0.le hqle 8
  have hq12 : q ^ 12 ≤ (61 / 100 : ℝ) ^ 12 := pow_le_pow_left₀ hq0.le hqle 12
  have hq4le : q ^ 4 ≤ 61 / 100 :=
    (pow_le_pow_left₀ hq0.le hqle 4).trans (by norm_num)
  have hq9le : q ^ 9 ≤ 61 / 100 :=
    (pow_le_pow_left₀ hq0.le hqle 9).trans (by norm_num)
  -- exponentials at the four couplings are powers of `q`
  have hexp4 : Real.exp (-(4 * s)) = q ^ 4 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexp9 : Real.exp (-(9 * s)) = q ^ 9 := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- tail-bound each factor: `qᵏ/(1−qᵏ) ≤ (100/39)·qᵏ` since `1−qᵏ ≥ 39/100`
  have hden4pos : (0 : ℝ) < 1 - q ^ 4 := by linarith
  have hden9pos : (0 : ℝ) < 1 - q ^ 9 := by linarith
  have hdiv4 : q ^ 4 / (1 - q ^ 4) ≤ (100 / 39) * q ^ 4 := by
    rw [div_le_iff₀ hden4pos]
    nlinarith [mul_nonneg (pow_nonneg hq0.le 4)
      (by linarith : (0 : ℝ) ≤ 61 / 100 - q ^ 4)]
  have hdiv9 : q ^ 9 / (1 - q ^ 9) ≤ (100 / 39) * q ^ 9 := by
    rw [div_le_iff₀ hden9pos]
    nlinarith [mul_nonneg (pow_nonneg hq0.le 9)
      (by linarith : (0 : ℝ) ≤ 61 / 100 - q ^ 9)]
  have hA : theta (4 * s) ≤ 1 + (200 / 39) * q ^ 4 := by
    have h := theta_le (4 * s) (by linarith)
    rw [hexp4] at h
    linarith
  have hB : theta (9 * s) ≤ 1 + (200 / 39) * q ^ 9 := by
    have h := theta_le (9 * s) (by linarith)
    rw [hexp9] at h
    linarith
  have hC : 1 + 2 * q ≤ theta s := by
    have h := theta_ge s hs0
    rw [← hq] at h
    linarith
  have hD : (1 : ℝ) < theta (36 * s) := theta_gt_one (36 * s) (by linarith)
  -- rational arithmetic closes: the coefficient of `q` on the left is < 2
  have hprod : theta (4 * s) * theta (9 * s)
      ≤ (1 + (200 / 39) * q ^ 4) * (1 + (200 / 39) * q ^ 9) :=
    mul_le_mul hA hB (theta_pos (9 * s) (by linarith)).le (by positivity)
  have hmid : (1 + (200 / 39) * q ^ 4) * (1 + (200 / 39) * q ^ 9)
      < 1 + 2 * q := by
    have e4 : q ^ 4 ≤ (61 / 100 : ℝ) ^ 3 * q := by
      calc q ^ 4 = q ^ 3 * q := by ring
        _ ≤ (61 / 100 : ℝ) ^ 3 * q := mul_le_mul_of_nonneg_right hq3 hq0.le
    have e9 : q ^ 9 ≤ (61 / 100 : ℝ) ^ 8 * q := by
      calc q ^ 9 = q ^ 8 * q := by ring
        _ ≤ (61 / 100 : ℝ) ^ 8 * q := mul_le_mul_of_nonneg_right hq8 hq0.le
    have e13 : q ^ 13 ≤ (61 / 100 : ℝ) ^ 12 * q := by
      calc q ^ 13 = q ^ 12 * q := by ring
        _ ≤ (61 / 100 : ℝ) ^ 12 * q := mul_le_mul_of_nonneg_right hq12 hq0.le
    have expand : (1 + (200 / 39) * q ^ 4) * (1 + (200 / 39) * q ^ 9)
        = 1 + ((200 / 39) * q ^ 4 + (200 / 39) * q ^ 9
            + (200 / 39) ^ 2 * q ^ 13) := by ring
    rw [expand]
    linarith [e4, e9, e13, hq0]
  calc theta (4 * s) * theta (9 * s)
      ≤ (1 + (200 / 39) * q ^ 4) * (1 + (200 / 39) * q ^ 9) := hprod
    _ < 1 + 2 * q := hmid
    _ ≤ theta s := hC
    _ = theta s * 1 := (mul_one _).symm
    _ < theta s * theta (36 * s) :=
        mul_lt_mul_of_pos_left hD (theta_pos s hs0)

/-- **The sign at (2, 3), all scales**: `θ(4s)·θ(9s) < θ(s)·θ(36s)`
for every `s > 0`. Small scales reflect into the large-scale branch
through the duality: because `4·9 = 1·36`, the Jacobi prefactors
`√(α/π)` cancel between the two sides, so the comparison at `s` is
equivalent to the comparison at `s′ = π²/(36s)` — and `π > 3` makes
the two regimes overlap. -/
theorem theta_prod_lt {s : ℝ} (hs : 0 < s) :
    theta (4 * s) * theta (9 * s) < theta s * theta (36 * s) := by
  rcases le_or_gt (1 / 2 : ℝ) s with h | h
  · exact theta_prod_lt_of_half_le h
  · -- reflect: `s′ = π²/(36s)` lands in the large-scale branch
    have hs' : (1 / 2 : ℝ) ≤ Real.pi ^ 2 / (36 * s) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [sq_nonneg (Real.pi - 3), Real.pi_gt_three]
    have hiff := theta_rect_lt_iff (t := s) (t' := Real.pi ^ 2 / (36 * s))
      (a := 2) (b := 3) hs (by norm_num) (by norm_num) (by norm_num)
    norm_num at hiff
    exact hiff.mpr (theta_prod_lt_of_half_le hs')

/-- **THE BIRTH CERTIFICATE** (M3): the defect at the smallest
incomparable pair is strictly negative at **every** scale —
`D_s(2, 3) < 0` for all `s > 0`. The defect vanishes on chains
(`defect_eq_zero_of_dvd`); off them, at `(2, 3)`, it carries a
strict sign uniformly in the scale. -/
theorem defect_two_three_neg {s : ℝ} (hs : 0 < s) :
    defect s 2 3 < 0 := by
  unfold defect
  rw [show Nat.gcd 2 3 = 1 from by decide,
    show Nat.lcm 2 3 = 6 from by decide,
    show (((2 : ℕ) : ℝ)) ^ 2 * s = 4 * s from by push_cast; ring,
    show (((3 : ℕ) : ℝ)) ^ 2 * s = 9 * s from by push_cast; ring,
    show (((1 : ℕ) : ℝ)) ^ 2 * s = s from by push_cast; ring,
    show (((6 : ℕ) : ℝ)) ^ 2 * s = 36 * s from by push_cast; ring]
  have hkey := theta_prod_lt hs
  have hp1 : (0 : ℝ) < theta (4 * s) := theta_pos (4 * s) (by linarith)
  have hp2 : (0 : ℝ) < theta (9 * s) := theta_pos (9 * s) (by linarith)
  have hp3 : (0 : ℝ) < theta s := theta_pos s hs
  have hp4 : (0 : ℝ) < theta (36 * s) := theta_pos (36 * s) (by linarith)
  have hlog := Real.log_lt_log (mul_pos hp1 hp2) hkey
  rw [Real.log_mul hp1.ne' hp2.ne', Real.log_mul hp3.ne' hp4.ne'] at hlog
  linarith

end Theaetetus
