import Theaetetus.FunctionalEquation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The fluctuation inequality: Fact 1 at large coupling

**Fact 1 of the Faulhuber–Steinerberger port** (README: the
ladder, rung 7). The target monotonicity of `α·θ′(α)/θ(α)` says,
in Gibbs language, that the coupling-weighted energy fluctuation
beats the mean energy: dividing its derivative numerator by `θ²`,

    α·Var(E) > ⟨E⟩.

At coupling `α ≥ π` this is proved by geometric domination of the
mode sums: the `k = 1` mode alone carries the second moment, and
everything above it is crushed by the ratio `4e^{−3α} ≤ 1/2000`.
The paper's stronger intermediate form
`0 < α·θ″ + θ′·θ − α·θ′²` (`theta_fluctuation_large`) gives the
actual log-derivative numerator `0 < α(θ″θ − θ′²) + θ′θ`
(`theta_logDeriv_numer_pos_large`) via `θ ≥ 1` and `θ″ > 0`. The
functional equation (`theta_logDeriv_dual`) transports this
half-line back through `α ↦ π²/α` in the next round. -/

namespace Theaetetus

/-- Positive-mode summability for every polynomial weight: the
`ℕ`-shifted restriction of the `ℤ`-moment series. -/
private theorem summable_shift (m : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ m * Real.exp (-α * ((k : ℝ) + 1) ^ 2)) := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b hab
    simpa using hab
  refine ((summable_pow_mul_exp m hα).comp_injective hinj).congr
    fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-- **The first derivative in positive modes**: the `ℤ`-series of
`θ′` collapses to twice the shifted `ℕ`-series, by evenness. -/
theorem thetaDeriv_eq_shift {α : ℝ} (hα : 0 < α) :
    thetaDeriv α
      = -(2 * ∑' k : ℕ,
          ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2)) := by
  set S : ℝ := ∑' k : ℕ,
    ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) with hS_def
  have hsm := summable_shift 2 hα
  have hf₁ : HasSum (fun n : ℕ =>
      ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2
        * Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hsm.hasSum.congr fun n => ?_
    push_cast
    rfl
  have hf₂ : HasSum (fun n : ℕ =>
      ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2
        * Real.exp (-α * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hsm.hasSum.congr fun n => ?_
    push_cast
    simp only [show ∀ y : ℝ, (-y) ^ 2 = y ^ 2 from fun y => by ring]
  have hZ : HasSum
      (fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2))
      (S + (((0 : ℤ) : ℝ) ^ 2 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2)) + S) :=
    HasSum.of_add_one_of_neg_add_one hf₁ hf₂
  have h := hZ.tsum_eq
  have h0 : ((0 : ℤ) : ℝ) ^ 2 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2) = 0 := by
    norm_num
  rw [h0] at h
  unfold thetaDeriv
  rw [h]
  ring

/-- **The second derivative in positive modes**. -/
theorem thetaDeriv2_eq_shift {α : ℝ} (hα : 0 < α) :
    thetaDeriv2 α
      = 2 * ∑' k : ℕ,
          ((k : ℝ) + 1) ^ 4 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
  set S : ℝ := ∑' k : ℕ,
    ((k : ℝ) + 1) ^ 4 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) with hS_def
  have hsm := summable_shift 4 hα
  have hf₁ : HasSum (fun n : ℕ =>
      ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 4
        * Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hsm.hasSum.congr fun n => ?_
    push_cast
    rfl
  have hf₂ : HasSum (fun n : ℕ =>
      ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 4
        * Real.exp (-α * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hsm.hasSum.congr fun n => ?_
    push_cast
    simp only [show ∀ y : ℝ, (-y) ^ 4 = y ^ 4 from fun y => by ring,
      show ∀ y : ℝ, (-y) ^ 2 = y ^ 2 from fun y => by ring]
  have hZ : HasSum
      (fun k : ℤ => (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2))
      (S + (((0 : ℤ) : ℝ) ^ 4 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2)) + S) :=
    HasSum.of_add_one_of_neg_add_one hf₁ hf₂
  have h := hZ.tsum_eq
  have h0 : ((0 : ℤ) : ℝ) ^ 4 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2) = 0 := by
    norm_num
  rw [h0] at h
  unfold thetaDeriv2
  rw [h]
  ring

/-- The `k = 1` mode alone carries the second moment from below. -/
private theorem le_tsum_quart_shift {α : ℝ} (hα : 0 < α) :
    Real.exp (-α)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
  have hle := (summable_shift 4 hα).sum_le_tsum {0}
    (fun j _ => by positivity)
  rw [Finset.sum_singleton] at hle
  calc Real.exp (-α)
      = (((0 : ℕ) : ℝ) + 1) ^ 4
        * Real.exp (-α * (((0 : ℕ) : ℝ) + 1) ^ 2) := by norm_num
    _ ≤ _ := hle

/-- Per-mode geometric domination of the first moment:
`(k+1)²·e^{−α(k+1)²} ≤ e^{−α}·(4e^{−3α})^k`, from `(k+1)² ≤ 4^k`
and `(k+1)² − 1 ≥ 3k`. -/
private theorem sq_shift_le_geo {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      ≤ Real.exp (-α) * (4 * Real.exp (-α) ^ 3) ^ k := by
  have hpow : ((k : ℝ) + 1) ^ 2 ≤ 4 ^ k := by
    induction k with
    | zero => norm_num
    | succ n ih =>
      push_cast
      nlinarith [ih, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)),
        sq_nonneg ((n : ℝ)), pow_succ (4 : ℝ) n]
  have hkk : (k : ℝ) ≤ ((k : ℝ)) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      nlinarith
  have hexp : Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      ≤ Real.exp (-α) * (Real.exp (-α) ^ 3) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hkk hα.le]
  calc ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      ≤ 4 ^ k * (Real.exp (-α) * (Real.exp (-α) ^ 3) ^ k) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-α) * (4 * Real.exp (-α) ^ 3) ^ k := by
        rw [mul_pow]
        ring

/-- Geometric bound on the first-moment sum. -/
private theorem tsum_sq_shift_le {α : ℝ} (hα : 0 < α)
    (hq : 4 * Real.exp (-α) ^ 3 < 1) :
    (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2))
      ≤ Real.exp (-α) * (1 - 4 * Real.exp (-α) ^ 3)⁻¹ := by
  have hq0 : (0 : ℝ) ≤ 4 * Real.exp (-α) ^ 3 := by positivity
  have hgeo : Summable (fun k : ℕ => (4 * Real.exp (-α) ^ 3) ^ k) :=
    summable_geometric_of_lt_one hq0 hq
  calc (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2))
      ≤ ∑' k : ℕ, Real.exp (-α) * (4 * Real.exp (-α) ^ 3) ^ k :=
        (summable_shift 2 hα).tsum_le_tsum (sq_shift_le_geo hα)
          (hgeo.mul_left _)
    _ = Real.exp (-α) * ∑' k : ℕ, (4 * Real.exp (-α) ^ 3) ^ k :=
        hgeo.tsum_mul_left _
    _ = Real.exp (-α) * (1 - 4 * Real.exp (-α) ^ 3)⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq]

/-- The vacuum-adjacent sum is dominated by the first moment:
each mode weight `(k+1)²` is at least 1. -/
private theorem tsum_exp_le_tsum_sq {α : ℝ} (hα : 0 < α) :
    (∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2))
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
  refine (summable_exp_sq_shift α hα).tsum_le_tsum (fun k => ?_)
    (summable_shift 2 hα)
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have h2 := mul_le_mul_of_nonneg_right h1
    (Real.exp_pos (-α * ((k : ℝ) + 1) ^ 2)).le
  linarith [h2]

/-- The single numeric input of the round: `e³ > 20`. -/
private theorem exp_cube_gt : (20 : ℝ) < Real.exp 1 ^ 3 := by
  have hE : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (7.389 : ℝ) < Real.exp 1 ^ 2 := by nlinarith [hE]
  nlinarith [hE, h2]

/-- At coupling `α ≥ 3` the Boltzmann factor is at most `1/20`. -/
private theorem exp_neg_le_of_three_le {α : ℝ} (hα : 3 ≤ α) :
    Real.exp (-α) ≤ 1 / 20 := by
  have h1 : Real.exp (-α) ≤ Real.exp (-3 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-3 : ℝ) ≤ 1 / 20 := by
    rw [Real.exp_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num,
      Real.exp_nat_mul, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_cube_gt.le
  linarith

/-- **Fact 1, strong form, at large coupling**: for `α ≥ π`,

    `0 < α·θ″(α) + θ′(α)·θ(α) − α·θ′(α)²`.

The `k = 1` mode of the second moment dominates every term the
first moment can produce: with `z = e^{−α} ≤ 1/20` the mode sums
satisfy `S₄ ≥ z` and `S₂, S₀ ≤ (51/50)·z`, and the margin closes
at the linear rate `α·z`. -/
theorem theta_fluctuation_large {α : ℝ} (hα : Real.pi ≤ α) :
    0 < α * thetaDeriv2 α + thetaDeriv α * theta α
      - α * thetaDeriv α ^ 2 := by
  have hα3 : (3 : ℝ) ≤ α := by linarith [Real.pi_gt_three]
  have hα0 : (0 : ℝ) < α := by linarith
  have hz0 : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have hz20 : Real.exp (-α) ≤ 1 / 20 := exp_neg_le_of_three_le hα3
  have hz3 : Real.exp (-α) ^ 3 ≤ 1 / 8000 := by
    nlinarith [hz0, hz20,
      mul_nonneg (sub_nonneg.mpr hz20) (sq_nonneg (Real.exp (-α))),
      mul_nonneg (sub_nonneg.mpr hz20) hz0.le]
  have hq1 : 4 * Real.exp (-α) ^ 3 < 1 := by linarith
  have hS4 := le_tsum_quart_shift hα0
  have hS2 := tsum_sq_shift_le hα0 hq1
  have hS0 := tsum_exp_le_tsum_sq hα0
  have hS2nn : (0 : ℝ)
      ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2) :=
    tsum_nonneg fun k => by positivity
  have hinv : (1 - 4 * Real.exp (-α) ^ 3)⁻¹ ≤ 51 / 50 := by
    rw [inv_eq_one_div]
    have h50 : (50 : ℝ) / 51 ≤ 1 - 4 * Real.exp (-α) ^ 3 := by linarith
    calc 1 / (1 - 4 * Real.exp (-α) ^ 3)
        ≤ 1 / ((50 : ℝ) / 51) := one_div_le_one_div_of_le (by norm_num) h50
      _ = 51 / 50 := by norm_num
  have hS2' : (∑' k : ℕ, ((k : ℝ) + 1) ^ 2
        * Real.exp (-α * ((k : ℝ) + 1) ^ 2))
      ≤ 51 / 50 * Real.exp (-α) := by
    calc (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * Real.exp (-α * ((k : ℝ) + 1) ^ 2))
        ≤ Real.exp (-α) * (1 - 4 * Real.exp (-α) ^ 3)⁻¹ := hS2
      _ ≤ Real.exp (-α) * (51 / 50) :=
          mul_le_mul_of_nonneg_left hinv hz0.le
      _ = 51 / 50 * Real.exp (-α) := by ring
  have hS0' : (∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2))
      ≤ 51 / 50 * Real.exp (-α) := hS0.trans hS2'
  have hθeq : theta α
      = 1 + 2 * ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
    linarith [theta_sub_one_eq α hα0]
  rw [thetaDeriv_eq_shift hα0, thetaDeriv2_eq_shift hα0, hθeq]
  nlinarith [hS2', hz0,
    mul_le_mul_of_nonneg_left hS4 hα0.le,
    mul_le_mul hS0' hS2' hS2nn (by positivity),
    mul_le_mul_of_nonneg_left
      (mul_le_mul hS2' hS2' hS2nn (by positivity)) hα0.le,
    mul_le_mul_of_nonneg_left hz20 (mul_nonneg hα0.le hz0.le),
    mul_le_mul_of_nonneg_left hz20 hz0.le,
    mul_le_mul_of_nonneg_right hα3 hz0.le]

/-- **Fact 1 at large coupling**: the numerator of the derivative
of `α·θ′(α)/θ(α)` is positive for `α ≥ π` — dividing by `θ²`,
the fluctuation inequality `α·Var(E) > ⟨E⟩`. Follows from the
strong form via `θ ≥ 1` and `θ″ > 0`. -/
theorem theta_logDeriv_numer_pos_large {α : ℝ} (hα : Real.pi ≤ α) :
    0 < α * (thetaDeriv2 α * theta α - thetaDeriv α ^ 2)
      + thetaDeriv α * theta α := by
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le Real.pi_pos hα
  have h1 := theta_fluctuation_large hα
  have hθ1 : 1 < theta α := theta_gt_one α hα0
  have hd2 : 0 < thetaDeriv2 α := thetaDeriv2_pos hα0
  nlinarith [mul_pos (mul_pos hα0 hd2) (sub_pos.mpr hθ1)]

end Theaetetus
