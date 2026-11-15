import Theaetetus.Fluctuation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The refined log-convexity at rank one

**The assembly of the Faulhuber–Steinerberger port.** Fact 1
(`theta_logDeriv_numer_pos_large`) makes `f(α) = α·θ′(α)/θ(α)` strictly increasing on `[π, ∞)` by
the mean value theorem. Fact 2 (`theta_logDeriv_dual`) says
`f(α) = −1/2 − f(π²/α)`, and `α ↦ π²/α` reverses order — so the
half-line reflects onto `(0, π]` with no further differentiation,
and `f` is strictly increasing on all of `(0, ∞)`
(`theta_logDeriv_strictMonoOn`). Integrated along the scale line
this is strict supermodularity of `log θ` in log-coordinates: the
difference `s ↦ log θ(a²s) − log θ(s)` is strictly increasing for
`a > 1`, which is the strict rectangle inequality

    θ(a²t)·θ(b²t) < θ(t)·θ((ab)²t)    (t > 0, a > 1, b > 1)

(`theta_rect_strict`) and, at `a = b`, the strict midpoint
inequality `θ(a²t)² < θ(t)·θ(a⁴t)` (`theta_sq_lt`) — the refined
log-convexity of the theta function, every scale, every ratio
above one. The rank-one curvature question is closed. -/

namespace Theaetetus

/-- The derivative of the scale-weighted logarithmic derivative:
`f = α·(θ′/θ)` has derivative `[α(θ″θ − θ′²) + θ′θ]/θ²` — the
fluctuation numerator over the square of the partition sum. -/
private theorem hasDerivAt_scaleLogDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun α : ℝ => α * (thetaDeriv α / theta α))
      ((x * (thetaDeriv2 x * theta x - thetaDeriv x ^ 2)
        + thetaDeriv x * theta x) / theta x ^ 2) x := by
  have hθ : theta x ≠ 0 := (theta_pos x hx).ne'
  have h : HasDerivAt (fun α : ℝ => α * (thetaDeriv α / theta α))
      (1 * (thetaDeriv x / theta x)
        + x * ((thetaDeriv2 x * theta x - thetaDeriv x * thetaDeriv x)
          / theta x ^ 2)) x :=
    (hasDerivAt_id x).mul
      ((hasDerivAt_thetaDeriv hx).div (hasDerivAt_theta hx) hθ)
  convert h using 1
  field_simp [hθ]
  ring

/-- **Global strict monotonicity** of `α·θ′(α)/θ(α)`: Fact 1
covers `[π, ∞)`, and the functional equation reflects it below
`π`. This is the Faulhuber–Steinerberger monotonicity in the
repo normalization, on every positive coupling. -/
theorem theta_logDeriv_strictMonoOn :
    StrictMonoOn (fun α : ℝ => α * (thetaDeriv α / theta α))
      (Set.Ioi 0) := by
  -- the large-coupling half-line, by the mean value theorem
  have hhi : StrictMonoOn (fun α : ℝ => α * (thetaDeriv α / theta α))
      (Set.Ici Real.pi) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun x hx => ?_) (fun x hx => ?_)
    · exact (hasDerivAt_scaleLogDeriv
        (lt_of_lt_of_le Real.pi_pos (Set.mem_Ici.mp hx))).continuousAt
        |>.continuousWithinAt
    · rw [interior_Ici] at hx
      have hπx : Real.pi < x := Set.mem_Ioi.mp hx
      have hx0 : (0 : ℝ) < x := Real.pi_pos.trans hπx
      rw [(hasDerivAt_scaleLogDeriv hx0).deriv]
      exact div_pos (theta_logDeriv_numer_pos_large hπx.le)
        (pow_pos (theta_pos x hx0) 2)
  -- the reflection transports the small-coupling half
  have hlow : ∀ p q : ℝ, 0 < p → p < q → q ≤ Real.pi →
      p * (thetaDeriv p / theta p) < q * (thetaDeriv q / theta q) := by
    intro p q hp hpq hqπ
    have hq : (0 : ℝ) < q := hp.trans hpq
    have hπq : Real.pi ≤ Real.pi ^ 2 / q := by
      rw [le_div_iff₀ hq]
      nlinarith [mul_le_mul_of_nonneg_left hqπ Real.pi_pos.le]
    have hlt : Real.pi ^ 2 / q < Real.pi ^ 2 / p := by
      have h1 : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp hpq
      have h2 := mul_lt_mul_of_pos_left h1
        (show (0 : ℝ) < Real.pi ^ 2 by positivity)
      rw [mul_one_div, mul_one_div] at h2
      exact h2
    have h3 : Real.pi ^ 2 / q
          * (thetaDeriv (Real.pi ^ 2 / q) / theta (Real.pi ^ 2 / q))
        < Real.pi ^ 2 / p
          * (thetaDeriv (Real.pi ^ 2 / p) / theta (Real.pi ^ 2 / p)) :=
      hhi (Set.mem_Ici.mpr hπq) (Set.mem_Ici.mpr (hπq.trans hlt.le)) hlt
    have hdp := theta_logDeriv_dual hp
    have hdq := theta_logDeriv_dual hq
    linarith [hdp, hdq, h3]
  -- glue the halves at the fixed point
  intro a ha b hb hab
  rcases le_or_gt b Real.pi with hbπ | hπb
  · exact hlow a b (Set.mem_Ioi.mp ha) hab hbπ
  · rcases lt_or_ge a Real.pi with haπ | hπa
    · show a * (thetaDeriv a / theta a) < b * (thetaDeriv b / theta b)
      have h1 : a * (thetaDeriv a / theta a)
          < Real.pi * (thetaDeriv Real.pi / theta Real.pi) :=
        hlow a Real.pi (Set.mem_Ioi.mp ha) haπ le_rfl
      have h2 : Real.pi * (thetaDeriv Real.pi / theta Real.pi)
          < b * (thetaDeriv b / theta b) :=
        hhi (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hπb.le) hπb
      linarith
    · exact hhi (Set.mem_Ici.mpr hπa) (Set.mem_Ici.mpr (hπa.trans hab.le)) hab

/-- **The strict rectangle inequality**:
at every scale, spreading the legs strictly loses to the corner
pair — `θ(a²t)·θ(b²t) < θ(t)·θ((ab)²t)` for `a, b > 1`. The
difference `s ↦ log θ(a²s) − log θ(s)` strictly increases because
its derivative is `(f(a²s) − f(s))/s` with `f` strictly monotone;
evaluate it at `t < b²t` and exponentiate. -/
theorem theta_rect_strict {t a b : ℝ} (ht : 0 < t) (ha : 1 < a)
    (hb : 1 < b) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t)
      < theta t * theta ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have ha2 : (1 : ℝ) < a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have hb2 : (1 : ℝ) < b ^ 2 := by nlinarith [sq_nonneg (b - 1)]
  -- the scale-difference of log θ at ratio a², differentiated
  have hD : ∀ s : ℝ, 0 < s → HasDerivAt
      (fun y : ℝ => Real.log (theta (a ^ 2 * y)) - Real.log (theta y))
      (thetaDeriv (a ^ 2 * s) * a ^ 2 / theta (a ^ 2 * s)
        - thetaDeriv s / theta s) s := by
    intro s hs
    have hρs : (0 : ℝ) < a ^ 2 * s := mul_pos (pow_pos ha0 2) hs
    have hθ1 : theta (a ^ 2 * s) ≠ 0 := (theta_pos _ hρs).ne'
    have hθ2 : theta s ≠ 0 := (theta_pos _ hs).ne'
    have hinner : HasDerivAt (fun y : ℝ => a ^ 2 * y) (a ^ 2) s := by
      simpa using (hasDerivAt_id s).const_mul (a ^ 2)
    have hcomp : HasDerivAt (fun y : ℝ => theta (a ^ 2 * y))
        (thetaDeriv (a ^ 2 * s) * a ^ 2) s :=
      (hasDerivAt_theta hρs).comp s hinner
    exact (hcomp.log hθ1).sub ((hasDerivAt_theta hs).log hθ2)
  -- the difference strictly increases on (0, ∞)
  have hDmono : StrictMonoOn
      (fun y : ℝ => Real.log (theta (a ^ 2 * y)) - Real.log (theta y))
      (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi _)
      (fun x hx => ?_) (fun x hx => ?_)
    · exact (hD x (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
    · rw [interior_Ioi] at hx
      have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
      have hρx0 : (0 : ℝ) < a ^ 2 * x := mul_pos (pow_pos ha0 2) hx0
      rw [(hD x hx0).deriv]
      have hxρx : x < a ^ 2 * x := by
        nlinarith [mul_pos hx0 (sub_pos.mpr ha2)]
      have h : x * (thetaDeriv x / theta x)
          < (a ^ 2 * x) * (thetaDeriv (a ^ 2 * x) / theta (a ^ 2 * x)) :=
        theta_logDeriv_strictMonoOn (Set.mem_Ioi.mpr hx0)
          (Set.mem_Ioi.mpr hρx0) hxρx
      have e2 : x * (thetaDeriv (a ^ 2 * x) * a ^ 2 / theta (a ^ 2 * x))
          = (a ^ 2 * x) * (thetaDeriv (a ^ 2 * x) / theta (a ^ 2 * x)) := by
        ring
      have h' : x * (thetaDeriv x / theta x)
          < x * (thetaDeriv (a ^ 2 * x) * a ^ 2 / theta (a ^ 2 * x)) := by
        rw [e2]
        exact h
      have h'' := lt_of_mul_lt_mul_left h' hx0.le
      linarith
  -- evaluate at t < b²t and exponentiate
  have htb : t < b ^ 2 * t := by
    nlinarith [mul_pos ht (sub_pos.mpr hb2)]
  have hkey : Real.log (theta (a ^ 2 * t)) - Real.log (theta t)
      < Real.log (theta (a ^ 2 * (b ^ 2 * t)))
        - Real.log (theta (b ^ 2 * t)) :=
    hDmono (Set.mem_Ioi.mpr ht)
      (Set.mem_Ioi.mpr (mul_pos (pow_pos hb0 2) ht)) htb
  rw [show a ^ 2 * (b ^ 2 * t) = (a * b) ^ 2 * t by ring] at hkey
  have hA : (0 : ℝ) < theta (a ^ 2 * t) * theta (b ^ 2 * t) :=
    mul_pos (theta_pos _ (mul_pos (pow_pos ha0 2) ht))
      (theta_pos _ (mul_pos (pow_pos hb0 2) ht))
  have hB : (0 : ℝ) < theta t * theta ((a * b) ^ 2 * t) :=
    mul_pos (theta_pos _ ht)
      (theta_pos _ (mul_pos (pow_pos (mul_pos ha0 hb0) 2) ht))
  have h1 : Real.log (theta (a ^ 2 * t) * theta (b ^ 2 * t))
      < Real.log (theta t * theta ((a * b) ^ 2 * t)) := by
    rw [Real.log_mul (theta_pos _ (mul_pos (pow_pos ha0 2) ht)).ne'
        (theta_pos _ (mul_pos (pow_pos hb0 2) ht)).ne',
      Real.log_mul (theta_pos _ ht).ne'
        (theta_pos _ (mul_pos (pow_pos (mul_pos ha0 hb0) 2) ht)).ne']
    linarith
  have h2 := Real.exp_lt_exp.mpr h1
  rwa [Real.exp_log hA, Real.exp_log hB] at h2

/-- **The strict midpoint inequality**: the
refined log-convexity `θ(a²t)² < θ(t)·θ(a⁴t)` at every scale and
every ratio `a > 1` — the strict form of `theta_sq_le`, no longer
confined to `a ≥ 2`. -/
theorem theta_sq_lt {t a : ℝ} (ht : 0 < t) (ha : 1 < a) :
    theta (a ^ 2 * t) ^ 2 < theta t * theta (a ^ 4 * t) := by
  have h := theta_rect_strict ht ha ha
  rw [show (a * a) ^ 2 * t = a ^ 4 * t by ring] at h
  nlinarith [h]

end Theaetetus
