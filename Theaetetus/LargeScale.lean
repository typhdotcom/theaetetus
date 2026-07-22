import Theaetetus.Pairing

/-! # The deep-scale limit of the pairing

**The normalized asymptotic** (README: Q4, toward rungs 5–6): at
large scale the pairing of a coprime pair is carried entirely by
the base mode,

    e^t · ⟨p, q⟩_t → 2    (`tendsto_exp_mul_pairing`).

The chain: the first mode carries the excess of `θ` exactly
(`tendsto_exp_mul_theta_sub_one`), so `θ → 1` at saturation
(`tendsto_theta_atTop`) and the base factor obeys
`e^t·log θ(t) → 2` (`tendsto_exp_mul_log_theta`), while every
resolved factor `log θ(ct)` with `c > 1` is exponentially
negligible against it (`tendsto_exp_mul_log_theta_shift`). The
pairing is the four-term combination, and only the base survives.

Through the reflection `pairing_scale_even`, this large-scale law
is also the small-scale law: as `s → 0` each coprime entry equals
`2e^{−σ}(1 + o(1))` at its own dual scale `σ = π²/(s·p²q²)` — the
hierarchical separation driving the small-scale chamber (rung 6)
and the saturation flattening driving the large-scale chamber
(rung 5). -/

namespace Theaetetus

open Filter Topology

/-- **The first mode carries the excess exactly**:
`e^t·(θ(t) − 1) → 2`. -/
theorem tendsto_exp_mul_theta_sub_one :
    Tendsto (fun t : ℝ => Real.exp t * (theta t - 1)) atTop (𝓝 2) := by
  have hupper : Tendsto (fun t : ℝ => 2 / (1 - Real.exp (-t)))
      atTop (𝓝 2) := by
    have h := (tendsto_const_nhds (α := ℝ) (x := (2 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        Real.tendsto_exp_neg_atTop_nhds_zero) (by norm_num)
    norm_num at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := theta_ge t ht
    have hexp : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos t]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := theta_le t ht
    have hexp : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp t * (theta t - 1)
        ≤ Real.exp t * (2 * (Real.exp (-t) / (1 - Real.exp (-t)))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos t).le
      _ = 2 * (Real.exp t * Real.exp (-t)) / (1 - Real.exp (-t)) := by
          ring
      _ = 2 / (1 - Real.exp (-t)) := by rw [hexp]; norm_num

/-- **Saturation of the base**: `θ(t) → 1` as `t → ∞`. -/
theorem tendsto_theta_atTop : Tendsto theta atTop (𝓝 1) := by
  have h : Tendsto
      (fun t : ℝ => Real.exp (-t) * (Real.exp t * (theta t - 1)) + 1)
      atTop (𝓝 (0 * 2 + 1)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.mul
      tendsto_exp_mul_theta_sub_one).add tendsto_const_nhds
  norm_num at h
  exact h.congr fun t => by
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (theta t - 1) * hexp

/-- **The base factor at speed one**: `e^t·log θ(t) → 2`. -/
theorem tendsto_exp_mul_log_theta :
    Tendsto (fun t : ℝ => Real.exp t * Real.log (theta t))
      atTop (𝓝 2) := by
  have hlow : Tendsto
      (fun t : ℝ => Real.exp t * (theta t - 1) * (theta t)⁻¹)
      atTop (𝓝 2) := by
    have h := tendsto_exp_mul_theta_sub_one.mul
      (tendsto_theta_atTop.inv₀ one_ne_zero)
    norm_num at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
    tendsto_exp_mul_theta_sub_one
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hθ : 0 < theta t := theta_pos t ht
    have hlog := Real.one_sub_inv_le_log_of_pos hθ
    calc Real.exp t * (theta t - 1) * (theta t)⁻¹
        = Real.exp t * ((theta t - 1) * (theta t)⁻¹) := by ring
      _ = Real.exp t * (1 - (theta t)⁻¹) := by
          rw [sub_mul, mul_inv_cancel₀ hθ.ne', one_mul]
      _ ≤ Real.exp t * Real.log (theta t) :=
          mul_le_mul_of_nonneg_left hlog (Real.exp_pos t).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (theta_pos t ht)) (Real.exp_pos t).le

/-- **Resolved factors are negligible**: for a coupling ratio
`c > 1`, `e^t·log θ(ct) → 0` — exponential separation between the
base mode and every resolved mode. -/
theorem tendsto_exp_mul_log_theta_shift {c : ℝ} (hc : 1 < c) :
    Tendsto (fun t : ℝ => Real.exp t * Real.log (theta (c * t)))
      atTop (𝓝 0) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hnum : Tendsto (fun t : ℝ => Real.exp ((1 - c) * t))
      atTop (𝓝 0) := by
    have hpos : Tendsto (fun t : ℝ => (c - 1) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
    have hmul : Tendsto (fun t : ℝ => (1 - c) * t) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp hpos).congr fun t => by
        simp only [Function.comp_apply]
        ring
    exact Real.tendsto_exp_atBot.comp hmul
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-(c * t)))
      atTop (𝓝 1) := by
    have hct : Tendsto (fun t : ℝ => c * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc0 tendsto_id
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hct)
    norm_num at h
    exact h
  have hupper : Tendsto
      (fun t : ℝ => 2 * Real.exp ((1 - c) * t) / (1 - Real.exp (-(c * t))))
      atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul hnum).div hden
      one_ne_zero
    norm_num at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h1 : (1 : ℝ) ≤ theta (c * t) :=
      (theta_gt_one _ (by positivity)).le
    exact mul_nonneg (Real.exp_pos t).le (Real.log_nonneg h1)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hct : (0 : ℝ) < c * t := by positivity
    have hlog := Real.log_le_sub_one_of_pos (theta_pos _ hct)
    have hle := theta_le (c * t) hct
    have hexp : Real.exp t * Real.exp (-(c * t)) = Real.exp ((1 - c) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp t * Real.log (theta (c * t))
        ≤ Real.exp t * (theta (c * t) - 1) :=
          mul_le_mul_of_nonneg_left hlog (Real.exp_pos t).le
      _ ≤ Real.exp t * (2 * (Real.exp (-(c * t)) / (1 - Real.exp (-(c * t))))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos t).le
      _ = 2 * (Real.exp t * Real.exp (-(c * t))) / (1 - Real.exp (-(c * t))) := by
          ring
      _ = 2 * Real.exp ((1 - c) * t) / (1 - Real.exp (-(c * t))) := by
          rw [hexp]

/-- **THE NORMALIZED PAIRING LIMIT**: for a coprime pair of
resolutions `p, q ≥ 2`, `e^t·⟨p,q⟩_t → 2` — at deep scale the
pairing is exactly twice the base mode. Only `log θ(t)` survives
the normalization; the three resolved factors are exponentially
separated. -/
theorem tendsto_exp_mul_pairing {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hco : Nat.Coprime p q) :
    Tendsto (fun t : ℝ => Real.exp t * pairing t p q) atTop (𝓝 2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp1 : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hq1 : (1 : ℝ) < (q : ℝ) ^ 2 := by nlinarith
  have hpq1 : (1 : ℝ) < ((p : ℝ) * (q : ℝ)) ^ 2 := by nlinarith
  have h := ((tendsto_exp_mul_log_theta.add
      (tendsto_exp_mul_log_theta_shift hpq1)).sub
      (tendsto_exp_mul_log_theta_shift hp1)).sub
      (tendsto_exp_mul_log_theta_shift hq1)
  norm_num at h
  exact h.congr fun t => by
    unfold pairing
    rw [defect_coprime hco]
    ring

end Theaetetus
