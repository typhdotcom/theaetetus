import Theaetetus.Gibbs

/-! # The functional equation: the reflection law differentiated

**Fact 2 of the Faulhuber–Steinerberger port** (README: the
ladder, rung 7). Squaring the duality `θ(π²/α) = √(α/π)·θ(α)`
removes the square root; differentiating the squared identity
through the Gibbs bridge and cancelling common factors yields the
functional equation of the logarithmic derivative

    α·θ′(α)/θ(α) + (π²/α)·θ′(π²/α)/θ(π²/α) = −1/2

(`theta_logDeriv_dual`) — the reflection law in infinitesimal
form. This is the transport map of rung 7: monotonicity of
`α·θ′(α)/θ(α)` on a half-line `[c, ∞)` propagates through
`α ↦ π²/α` to the interval `(0, π²/c]`, which is how Fact 1's
large-coupling estimate will reach the origin. At the fixed point
`α = π` the equation pins the anchor `θ′(π) = −θ(π)/(4π)`
(`thetaDeriv_pi`). -/

namespace Theaetetus

open Filter Topology

/-- The duality squared: the prefactor turns rational, no `rpow`
survives. -/
private theorem theta_sq_dual {x : ℝ} (hx : 0 < x) :
    theta (Real.pi ^ 2 / x) * theta (Real.pi ^ 2 / x)
      = x / Real.pi * (theta x * theta x) := by
  have h2 : (x / Real.pi) ^ ((1 : ℝ) / 2)
      * (x / Real.pi) ^ ((1 : ℝ) / 2) = x / Real.pi := by
    rw [← Real.rpow_add (div_pos hx Real.pi_pos)]
    norm_num
  rw [theta_duality_real x hx]
  linear_combination theta x * theta x * h2

/-- **Fact 2, the functional equation**: the logarithmic
derivative of `θ` sums to `−1/2` across the reflection
`α ↦ π²/α`. Differentiate the squared duality
`θ(π²/α)² = (α/π)·θ(α)²` and divide by it. -/
theorem theta_logDeriv_dual {α : ℝ} (hα : 0 < α) :
    α * (thetaDeriv α / theta α)
      + Real.pi ^ 2 / α
        * (thetaDeriv (Real.pi ^ 2 / α) / theta (Real.pi ^ 2 / α))
      = -(1 / 2) := by
  have hβ : 0 < Real.pi ^ 2 / α := div_pos (pow_pos Real.pi_pos 2) hα
  have hA : 0 < theta α := theta_pos α hα
  have hB : 0 < theta (Real.pi ^ 2 / α) := theta_pos _ hβ
  -- the reflected side, differentiated through the Gibbs bridge
  have hinner : HasDerivAt (fun x : ℝ => Real.pi ^ 2 / x)
      (Real.pi ^ 2 * -(α ^ 2)⁻¹) α := by
    simp only [div_eq_mul_inv]
    exact (hasDerivAt_inv (ne_of_gt hα)).const_mul (Real.pi ^ 2)
  have hcomp := (hasDerivAt_theta hβ).comp α hinner
  have hL := hcomp.mul hcomp
  -- the flat side, differentiated
  have hs : HasDerivAt (fun x : ℝ => x / Real.pi) (1 / Real.pi) α :=
    (hasDerivAt_id α).div_const Real.pi
  have hθθ := (hasDerivAt_theta hα).mul (hasDerivAt_theta hα)
  have hR := hs.mul hθθ
  -- the two sides agree near α, so the derivatives agree at α
  have hE : (fun x : ℝ =>
        theta (Real.pi ^ 2 / x) * theta (Real.pi ^ 2 / x))
      =ᶠ[𝓝 α] fun x : ℝ => x / Real.pi * (theta x * theta x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hα)] with x hx
    exact theta_sq_dual hx
  have hkey := hL.unique (hR.congr_of_eventuallyEq hE)
  -- clear denominators in both inputs
  have hkey' : -(2 * Real.pi ^ 3
        * (theta (Real.pi ^ 2 / α) * thetaDeriv (Real.pi ^ 2 / α)))
      = α ^ 2 * (theta α * theta α)
        + 2 * α ^ 3 * (theta α * thetaDeriv α) := by
    simp only [Function.comp_apply, Pi.mul_apply] at hkey
    field_simp at hkey
    linarith
  have hB2' : Real.pi
        * (theta (Real.pi ^ 2 / α) * theta (Real.pi ^ 2 / α))
      = α * (theta α * theta α) := by
    have h := theta_sq_dual hα
    field_simp at h
    linarith
  -- the polynomial form of the functional equation, then divide
  have hT : Real.pi * theta (Real.pi ^ 2 / α)
      * (2 * α ^ 2 * (thetaDeriv α * theta (Real.pi ^ 2 / α))
        + 2 * Real.pi ^ 2 * (theta α * thetaDeriv (Real.pi ^ 2 / α))
        + α * (theta α * theta (Real.pi ^ 2 / α))) = 0 := by
    linear_combination (-(theta α)) * hkey'
      + (2 * α ^ 2 * thetaDeriv α + α * theta α) * hB2'
  have hT0 : 2 * α ^ 2 * (thetaDeriv α * theta (Real.pi ^ 2 / α))
      + 2 * Real.pi ^ 2 * (theta α * thetaDeriv (Real.pi ^ 2 / α))
      + α * (theta α * theta (Real.pi ^ 2 / α)) = 0 :=
    (mul_eq_zero.mp hT).resolve_left
      (mul_ne_zero Real.pi_ne_zero hB.ne')
  have hexpand : α * (thetaDeriv α / theta α)
        + Real.pi ^ 2 / α
          * (thetaDeriv (Real.pi ^ 2 / α) / theta (Real.pi ^ 2 / α))
        + 1 / 2
      = (2 * α ^ 2 * (thetaDeriv α * theta (Real.pi ^ 2 / α))
          + 2 * Real.pi ^ 2 * (theta α * thetaDeriv (Real.pi ^ 2 / α))
          + α * (theta α * theta (Real.pi ^ 2 / α)))
        / (2 * α * (theta α * theta (Real.pi ^ 2 / α))) := by
    field_simp
  rw [hT0, zero_div] at hexpand
  linarith

/-- **The anchor**: at the fixed point of the reflection the
functional equation pins the derivative, `θ′(π) = −θ(π)/(4π)`. -/
theorem thetaDeriv_pi :
    thetaDeriv Real.pi = -(theta Real.pi / (4 * Real.pi)) := by
  have h := theta_logDeriv_dual Real.pi_pos
  have hππ : Real.pi ^ 2 / Real.pi = Real.pi := by
    rw [pow_two, mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
  rw [hππ] at h
  have hθ : theta Real.pi ≠ 0 := (theta_pos Real.pi Real.pi_pos).ne'
  have h2 : Real.pi * (thetaDeriv Real.pi / theta Real.pi)
      = -(1 / 4) := by linarith
  field_simp at h2
  field_simp
  linarith

end Theaetetus
