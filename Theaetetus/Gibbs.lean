import Theaetetus.Theta
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # The Gibbs bridge: termwise derivatives of the primitive

**The derivative of `θ` is an energy moment.** Differentiating the
Boltzmann sum under the series gives

    θ′(α) = −∑ k²·e^{−αk²},    θ″(α) = ∑ k⁴·e^{−αk²}

(`hasDerivAt_theta`, `hasDerivAt_thetaDeriv`): the first and
second unnormalized moments of the energy `k²` under the Gibbs
weight — `θ′/θ = −⟨E⟩` and `θ″/θ = ⟨E²⟩`. Differentiation under
`∑'` is justified locally: on `(α/2, ∞)` the termwise derivatives
are dominated by the summable majorant at scale `α/2`
(`summable_pow_mul_exp`).

This is the bridge every derivative statement downstream crosses:
the Faulhuber–Steinerberger monotonicity
(`theta_logDeriv_strictMonoOn`) needs `θ′` and
`θ″` as series to estimate, and the higher-rank fluctuation
inequality `β²Var(E) ≥ β⟨E⟩` is a statement about exactly these
moments. -/

namespace Theaetetus

/-- The first derivative of `θ` as a Boltzmann series: minus the
first energy moment. -/
noncomputable def thetaDeriv (α : ℝ) : ℝ :=
  -∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)

/-- The second derivative of `θ`: the second energy moment. -/
noncomputable def thetaDeriv2 (α : ℝ) : ℝ :=
  ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)

/-- **Moment summability**: every polynomial-weighted Boltzmann
series converges at positive coupling. -/
theorem summable_pow_mul_exp (m : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun k : ℤ => (k : ℝ) ^ m * Real.exp (-α * (k : ℝ) ^ 2)) := by
  have hr1 : Real.exp (-α) < 1 := by
    have h := Real.exp_lt_exp.mpr (neg_lt_zero.mpr hα)
    rwa [Real.exp_zero] at h
  have hr0 : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ m * Real.exp (-α) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one m
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ m * Real.exp (-α * (n : ℝ) ^ 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hgeo
    intro n
    have hle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        nlinarith
    have hexp : Real.exp (-α * (n : ℝ) ^ 2) ≤ Real.exp (-α) ^ n := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hle)]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  refine Summable.of_nat_of_neg (hnat.congr fun n => ?_)
    ((hnat.mul_left ((-1 : ℝ) ^ m)).congr fun n => ?_)
  · push_cast
    ring
  · push_cast
    rw [neg_sq, neg_pow]
    ring

/-- **The first derivative** of the theta function, termwise:
`θ′(α) = −∑ k²e^{−αk²}` at every positive coupling. -/
theorem hasDerivAt_theta {α : ℝ} (hα : 0 < α) :
    HasDerivAt theta (thetaDeriv α) α := by
  have hhalf : (0 : ℝ) < α / 2 := by linarith
  have hmem : α ∈ Set.Ioi (α / 2) := Set.mem_Ioi.mpr (by linarith)
  have hg : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      HasDerivAt (fun x : ℝ => Real.exp (-x * (k : ℝ) ^ 2))
        (Real.exp (-y * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2)) y := by
    intro k y _
    exact (((hasDerivAt_id y).neg).mul_const _).exp
  have hg' : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      ‖Real.exp (-y * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2)‖
        ≤ (k : ℝ) ^ 2 * Real.exp (-(α / 2) * (k : ℝ) ^ 2) := by
    intro k y hy
    rw [Set.mem_Ioi] at hy
    have he : |Real.exp (-y * (k : ℝ) ^ 2)| = Real.exp (-y * (k : ℝ) ^ 2) :=
      abs_of_pos (Real.exp_pos _)
    have hk : |(-1 : ℝ) * (k : ℝ) ^ 2| = (k : ℝ) ^ 2 := by
      rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs, abs_mul, he, hk]
    have hmono : Real.exp (-y * (k : ℝ) ^ 2)
        ≤ Real.exp (-(α / 2) * (k : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (k : ℝ)]
    calc Real.exp (-y * (k : ℝ) ^ 2) * (k : ℝ) ^ 2
        ≤ Real.exp (-(α / 2) * (k : ℝ) ^ 2) * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
      _ = (k : ℝ) ^ 2 * Real.exp (-(α / 2) * (k : ℝ) ^ 2) := mul_comm _ _
  have key := hasDerivAt_tsum_of_isPreconnected
    (summable_pow_mul_exp 2 hhalf) isOpen_Ioi isPreconnected_Ioi
    hg hg' hmem (summable_theta α hα) hmem
  have hval : (∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2))
      = thetaDeriv α := by
    unfold thetaDeriv
    rw [← tsum_neg]
    exact tsum_congr fun k => by ring
  rw [hval] at key
  exact key

/-- **The second derivative**, termwise: `θ″(α) = ∑ k⁴e^{−αk²}`
at every positive coupling — differentiating the moment series
again. -/
theorem hasDerivAt_thetaDeriv {α : ℝ} (hα : 0 < α) :
    HasDerivAt thetaDeriv (thetaDeriv2 α) α := by
  have hhalf : (0 : ℝ) < α / 2 := by linarith
  have hmem : α ∈ Set.Ioi (α / 2) := Set.mem_Ioi.mpr (by linarith)
  have hg : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      HasDerivAt (fun x : ℝ => (k : ℝ) ^ 2 * Real.exp (-x * (k : ℝ) ^ 2))
        ((k : ℝ) ^ 2 * (Real.exp (-y * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2))) y := by
    intro k y _
    exact ((((hasDerivAt_id y).neg).mul_const _).exp).const_mul _
  have hg' : ∀ (k : ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      ‖(k : ℝ) ^ 2 * (Real.exp (-y * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2))‖
        ≤ (k : ℝ) ^ 4 * Real.exp (-(α / 2) * (k : ℝ) ^ 2) := by
    intro k y hy
    rw [Set.mem_Ioi] at hy
    have he : |Real.exp (-y * (k : ℝ) ^ 2)| = Real.exp (-y * (k : ℝ) ^ 2) :=
      abs_of_pos (Real.exp_pos _)
    have hk : |(-1 : ℝ) * (k : ℝ) ^ 2| = (k : ℝ) ^ 2 := by
      rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, he, hk,
      abs_of_nonneg (sq_nonneg (k : ℝ))]
    have hmono : Real.exp (-y * (k : ℝ) ^ 2)
        ≤ Real.exp (-(α / 2) * (k : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (k : ℝ)]
    calc (k : ℝ) ^ 2 * (Real.exp (-y * (k : ℝ) ^ 2) * (k : ℝ) ^ 2)
        ≤ (k : ℝ) ^ 2 * (Real.exp (-(α / 2) * (k : ℝ) ^ 2) * (k : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
      _ = (k : ℝ) ^ 4 * Real.exp (-(α / 2) * (k : ℝ) ^ 2) := by ring
  have key := hasDerivAt_tsum_of_isPreconnected
    (summable_pow_mul_exp 4 hhalf) isOpen_Ioi isPreconnected_Ioi
    hg hg' hmem (summable_pow_mul_exp 2 hα) hmem
  have hval : (∑' k : ℤ, (k : ℝ) ^ 2
        * (Real.exp (-α * (k : ℝ) ^ 2) * (-1 * (k : ℝ) ^ 2)))
      = -thetaDeriv2 α := by
    unfold thetaDeriv2
    rw [← tsum_neg]
    exact tsum_congr fun k => by ring
  rw [hval] at key
  have := key.neg
  rw [neg_neg] at this
  exact this

/-- The first derivative is strictly negative: energy decreases
the partition sum. -/
theorem thetaDeriv_neg {α : ℝ} (hα : 0 < α) : thetaDeriv α < 0 := by
  unfold thetaDeriv
  rw [neg_lt, neg_zero]
  exact (summable_pow_mul_exp 2 hα).tsum_pos (fun k => by positivity) 1
    (by norm_num [Real.exp_pos])

/-- The second moment is strictly positive. -/
theorem thetaDeriv2_pos {α : ℝ} (hα : 0 < α) : 0 < thetaDeriv2 α := by
  unfold thetaDeriv2
  exact (summable_pow_mul_exp 4 hα).tsum_pos (fun k => by positivity) 1
    (by norm_num [Real.exp_pos])

/-- The `deriv` form of the bridge. -/
theorem deriv_theta {α : ℝ} (hα : 0 < α) :
    deriv theta α = thetaDeriv α :=
  (hasDerivAt_theta hα).deriv

/-- **Strict decrease**: the theta function is strictly decreasing on
positive couplings, since its derivative is the negated second
moment. -/
theorem theta_strictAntiOn : StrictAntiOn theta (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (theta_continuousAt (Set.mem_Ioi.mp hx)).continuousWithinAt)
    fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [deriv_theta (Set.mem_Ioi.mp hx)]
  exact thetaDeriv_neg (Set.mem_Ioi.mp hx)

/-- Larger positive couplings suppress the nonzero modes: if
`0 < α < β`, then `θ(β) < θ(α)`. -/
theorem theta_lt_theta {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    theta β < theta α :=
  theta_strictAntiOn (Set.mem_Ioi.mpr hα)
    (Set.mem_Ioi.mpr (hα.trans hαβ)) hαβ

end Theaetetus
