import Theaetetus.Submodular

/-! # Coarse Q5: the equal-leg midpoint inequality

**The `b → a` limit of the sign** (README: Q5 and the ladder,
rung 4). `theta_prod_lt_general` proves the strict cross-ratio
inequality for real legs `2 ≤ a < b`; sending `b → a⁺` through the
continuity of `θ` (`theta_continuousAt`) yields its equal-leg
boundary case

    θ(a²t)² ≤ θ(t)·θ(a⁴t),    2 ≤ a, 0 < t

(`theta_sq_le`) — in the log, midpoint convexity of
`H(u) = log θ(eᵘ)` at every location, at leg spacing `≥ 2·log 2`
(`log_theta_midpoint_le`). In particular every Q4 diagonal
correction `d_s(x_p) = log θ(s) − 2·log θ(p²s) + log θ(p⁴s)` is
nonnegative, since every prime has `x_p = log p ≥ log 2`.

Q5 at rank one is the conjecture that the hypothesis `2 ≤ a` —
which originates in integer incomparability — can be relaxed to
`1 < a`; the strict inequality degenerates at `a = b`, so the
non-strict equal-leg case is exactly the boundary the limit
reaches. -/

namespace Theaetetus

open Filter Topology

/-- **Coarse Q5** (rung 4): the equal-leg case of the theta
inequality, `θ(a²t)² ≤ θ(t)·θ(a⁴t)` for real `a ≥ 2` — the
`b → a⁺` limit of `theta_prod_lt_general`. -/
theorem theta_sq_le {t a : ℝ} (ht : 0 < t) (ha : 2 ≤ a) :
    theta (a ^ 2 * t) ^ 2 ≤ theta t * theta (a ^ 4 * t) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le two_pos ha
  -- continuity of both sides in the second leg, at `b = a`
  have hi1 : ContinuousAt (fun b : ℝ => b ^ 2 * t) a :=
    ((continuous_pow 2).mul continuous_const).continuousAt
  have hc1 : ContinuousAt (fun b : ℝ => theta (b ^ 2 * t)) a :=
    ContinuousAt.comp (f := fun b : ℝ => b ^ 2 * t) (x := a)
      (theta_continuousAt (show (0 : ℝ) < a ^ 2 * t by positivity)) hi1
  have hi2 : ContinuousAt (fun b : ℝ => (a * b) ^ 2 * t) a :=
    (((continuous_const.mul continuous_id).pow 2).mul continuous_const).continuousAt
  have hc2 : ContinuousAt (fun b : ℝ => theta ((a * b) ^ 2 * t)) a :=
    ContinuousAt.comp (f := fun b : ℝ => (a * b) ^ 2 * t) (x := a)
      (theta_continuousAt (show (0 : ℝ) < (a * a) ^ 2 * t by positivity)) hi2
  have hF : Tendsto (fun b : ℝ => theta (a ^ 2 * t) * theta (b ^ 2 * t))
      (nhdsWithin a (Set.Ioi a))
      (nhds (theta (a ^ 2 * t) * theta (a ^ 2 * t))) :=
    (continuousAt_const.mul hc1).tendsto.mono_left nhdsWithin_le_nhds
  have hG : Tendsto (fun b : ℝ => theta t * theta ((a * b) ^ 2 * t))
      (nhdsWithin a (Set.Ioi a))
      (nhds (theta t * theta (a ^ 4 * t))) := by
    have h : Tendsto (fun b : ℝ => theta t * theta ((a * b) ^ 2 * t))
        (nhdsWithin a (Set.Ioi a))
        (nhds (theta t * theta ((a * a) ^ 2 * t))) :=
      (continuousAt_const.mul hc2).tendsto.mono_left nhdsWithin_le_nhds
    rw [show (a * a) ^ 2 * t = a ^ 4 * t from by ring] at h
    exact h
  have hev : ∀ᶠ b in nhdsWithin a (Set.Ioi a),
      theta (a ^ 2 * t) * theta (b ^ 2 * t)
        ≤ theta t * theta ((a * b) ^ 2 * t) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (theta_prod_lt_general ht ha hb).le
  have hlim := le_of_tendsto_of_tendsto hF hG hev
  rw [pow_two]
  exact hlim

/-- **The midpoint inequality in the log** (the Q4 diagonal):
`2·log θ(a²t) ≤ log θ(t) + log θ(a⁴t)` for real `a ≥ 2` — every
diagonal correction of the prime kernel is nonnegative. -/
theorem log_theta_midpoint_le {t a : ℝ} (ht : 0 < t) (ha : 2 ≤ a) :
    2 * Real.log (theta (a ^ 2 * t))
      ≤ Real.log (theta t) + Real.log (theta (a ^ 4 * t)) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le two_pos ha
  have h := theta_sq_le ht ha
  have hlog := Real.log_le_log
    (pow_pos (theta_pos _ (by positivity)) 2) h
  rw [Real.log_pow, Real.log_mul (theta_pos t ht).ne'
    (theta_pos _ (by positivity)).ne'] at hlog
  push_cast at hlog
  linarith

end Theaetetus
