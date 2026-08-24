import Theaetetus.LogMassFourier
import Theaetetus.GramAsymptotics

/-! # The cluster normalization of the logarithmic mass

The shifted mass expands over the dual lattice with strictly positive
weights (`hasSum_massFourier_cos`). Dividing by the zero-frequency
weight puts that expansion in the form the logarithm can consume:

    gramMass M α x = zeroMode M α · (1 + residual M α x)

(`gramMass_eq_zeroMode_mul`), where the residual carries only the
nonzero dual modes (`hasSum_residual`) and is therefore controlled
uniformly by their total relative weight
(`abs_residual_le_totalWeight`).

That total weight is by definition the excess of the mass at the
origin over its zero mode (`totalWeight`), equivalently the residual
at the origin (`totalWeight_eq_residual_zero`), and it really is the
sum of the nonzero relative mode weights (`hasSum_totalWeight`). The
small-scale asymptotic of the Boltzmann sum therefore measures it: as
the coupling falls to zero the dual energies, which scale like
`π²/α`, spread out, the dual modes go sparse, and the weight vanishes
(`tendsto_totalWeight_nhdsGT_zero`). Below any threshold — in
particular below `1` — the logarithm of the mass therefore has a
convergent expansion in powers of the residual
(`hasSum_logMass_residual`), with a remainder after truncating at
order `K` bounded by the weight alone
(`abs_logMass_sub_partialSum_le`). Both are uniform in the shift.

What this exposes is the cluster structure: the `k`-th term is a
`k`-fold product of dual modes, so the Fourier coefficient of the
logarithm at a frequency `ν` collects the decompositions
`ν = ν₁ + ⋯ + ν_k`. Turning that reading into an identity between
coefficients needs the Fourier coefficient of a product — a
convolution theorem on the torus — together with the interchange of
the coefficient functional with this series. Neither is proved here,
and no nonvanishing statement is claimed. -/

namespace Theaetetus

open Filter Topology

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## The zero mode and the residual -/

/-- The zero-frequency dual weight of the shifted mass. -/
noncomputable def zeroMode (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  massFourierCoeff M α 0

theorem zeroMode_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    0 < zeroMode M α :=
  massFourierCoeff_pos hM hα 0

/-- The zero mode in closed form: the reciprocal square root of the
determinant of the rescaled form. -/
theorem zeroMode_eq (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) :
    zeroMode M α = (((α / Real.pi) • M).det)⁻¹ ^ ((1 : ℝ) / 2) := by
  show gaussFourierCoeff ((α / Real.pi) • M) 0 = _
  rw [gaussFourierCoeff]
  norm_num

/-- The relative weight of a dual mode. -/
noncomputable def modeWeight (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (m : Fin d → ℤ) : ℝ := massFourierCoeff M α m / zeroMode M α

theorem modeWeight_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (m : Fin d → ℤ) : 0 < modeWeight M α m :=
  div_pos (massFourierCoeff_pos hM hα m) (zeroMode_pos hM hα)

theorem modeWeight_zero (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    modeWeight M α 0 = 1 :=
  div_self (zeroMode_pos hM hα).ne'

/-- The residual field: the mass normalized by its zero mode, less
one. -/
noncomputable def residual (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (x : Fin d → ℝ) : ℝ := gramMass M α x / zeroMode M α - 1

/-- **The cluster normalization**. -/
theorem gramMass_eq_zeroMode_mul (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    gramMass M α x = zeroMode M α * (1 + residual M α x) := by
  have h0 : zeroMode M α ≠ 0 := (zeroMode_pos hM hα).ne'
  rw [residual]
  field_simp
  ring

/-! ## The residual carries only nonzero modes -/

/-- The normalized expansion: the mass over its zero mode is the sum
of the relative mode weights against the characters. -/
theorem hasSum_modeWeight_cos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        modeWeight M α m * Real.cos (2 * Real.pi * dualPairing m x))
      (1 + residual M α x) := by
  have h0 : zeroMode M α ≠ 0 := (zeroMode_pos hM hα).ne'
  have h := (hasSum_massFourier_cos hM hα x).div_const (zeroMode M α)
  have hval : gramMass M α x / zeroMode M α = 1 + residual M α x := by
    rw [residual]
    ring
  rw [hval] at h
  refine h.congr_fun fun m => ?_
  rw [modeWeight]
  ring

/-- The residual is the same sum with the zero mode removed: only
nonzero dual frequencies contribute. -/
theorem hasSum_residual (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        if m = 0 then 0
        else modeWeight M α m * Real.cos (2 * Real.pi * dualPairing m x))
      (residual M α x) := by
  have hz : modeWeight M α 0 * Real.cos (2 * Real.pi * dualPairing 0 x)
      = 1 := by
    rw [modeWeight_zero hM hα, show dualPairing (0 : Fin d → ℤ) x = 0 by
      simp [dualPairing]]
    norm_num
  have h := (hasSum_modeWeight_cos hM hα x).sub
    (hasSum_ite_eq (0 : Fin d → ℤ) (1 : ℝ))
  rw [show (1 : ℝ) + residual M α x - 1 = residual M α x by ring] at h
  refine h.congr_fun fun m => ?_
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, if_pos rfl, hz, sub_self]
  · rw [if_neg hm, if_neg hm, sub_zero]

/-! ## The total weight of the nonzero modes -/

/-- The total relative weight of the nonzero dual modes. -/
noncomputable def totalWeight (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  gramMass M α 0 / zeroMode M α - 1

theorem totalWeight_eq_residual_zero (M : Matrix (Fin d) (Fin d) ℝ)
    (α : ℝ) : totalWeight M α = residual M α 0 := rfl

/-- **The weight is a sum of weights**: the total weight is literally
the sum of the relative weights of the nonzero dual modes. This is
the `ℓ¹` control the mode sequence carries. -/
theorem hasSum_totalWeight (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasSum (fun m : Fin d → ℤ => if m = 0 then 0 else modeWeight M α m)
      (totalWeight M α) := by
  have h := hasSum_residual hM hα (0 : Fin d → ℝ)
  rw [← totalWeight_eq_residual_zero] at h
  refine h.congr_fun fun m => ?_
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm,
      show dualPairing m (0 : Fin d → ℝ) = 0 by simp [dualPairing]]
    norm_num

theorem totalWeight_nonneg (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    0 ≤ totalWeight M α := by
  refine (hasSum_totalWeight hM hα).nonneg fun m => ?_
  by_cases hm : m = 0
  · rw [if_pos hm]
  · rw [if_neg hm]
    exact (modeWeight_pos hM hα m).le

/-- **The uniform bound**: the residual never exceeds the total weight
of the nonzero modes, at any shift. -/
theorem abs_residual_le_totalWeight (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) : |residual M α x| ≤ totalWeight M α := by
  have hx := hasSum_residual hM hα x
  have h0 := hasSum_residual hM hα (0 : Fin d → ℝ)
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [neg_le]
    refine hasSum_le (fun m => ?_) hx.neg h0
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have hcos : Real.cos (2 * Real.pi * dualPairing m 0) = 1 := by
        rw [show dualPairing m (0 : Fin d → ℝ) = 0 by simp [dualPairing]]
        norm_num
      rw [hcos, mul_one]
      have := (modeWeight_pos hM hα m).le
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * dualPairing m x)]
  · refine hasSum_le (fun m => ?_) hx h0
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      have hcos : Real.cos (2 * Real.pi * dualPairing m 0) = 1 := by
        rw [show dualPairing m (0 : Fin d → ℝ) = 0 by simp [dualPairing]]
        norm_num
      rw [hcos, mul_one]
      have := (modeWeight_pos hM hα m).le
      nlinarith [Real.cos_le_one (2 * Real.pi * dualPairing m x)]

/-! ## The sparse-dual regime -/

private theorem det_scale_rpow (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    (((α / Real.pi) • M).det) ^ ((1 : ℝ) / 2)
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2) := by
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα Real.pi_pos
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.mul_rpow (by positivity) hM.det_pos.le]
  congr 1
  rw [← Real.rpow_natCast (α / Real.pi) d, ← Real.rpow_mul hc.le]
  congr 1
  ring

private theorem inv_zeroMode (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    (zeroMode M α)⁻¹
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2) := by
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα Real.pi_pos
  have hD : (0 : ℝ) < ((α / Real.pi) • M).det := (posDef_smul' hM hc).det_pos
  rw [zeroMode_eq, Real.inv_rpow hD.le, inv_inv, det_scale_rpow hM hα]

/-- The total weight in the determinant-normalized form the
small-scale asymptotic controls. -/
theorem totalWeight_eq_scaled (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    totalWeight M α
      = (α / Real.pi) ^ ((d : ℝ) / 2) * gramTheta M α
          * M.det ^ ((1 : ℝ) / 2) - 1 := by
  rw [totalWeight, gramMass_zero, div_eq_mul_inv, inv_zeroMode hM hα]
  ring

/-- **The sparse-dual, small-coupling regime**: as the coupling falls
to zero the nonzero dual modes lose all their weight, their energies
scaling like `π²/α`. This is the small-coupling Boltzmann asymptotic
read on the dual side. It controls small `α` only, and says nothing
about `α → ∞`. -/
theorem tendsto_totalWeight_nhdsGT_zero (hM : M.PosDef) :
    Tendsto (fun α : ℝ => totalWeight M α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmul := (tendsto_gramTheta_nhdsGT_zero hM).mul (tendsto_const_nhds
    (x := M.det ^ ((1 : ℝ) / 2)) (f := 𝓝[>] (0 : ℝ)))
  have hone : M.det ^ (-(1 : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hM.det_pos]
    norm_num
  rw [hone] at hmul
  have hsub := hmul.sub (tendsto_const_nhds (x := (1 : ℝ))
    (f := 𝓝[>] (0 : ℝ)))
  rw [sub_self] at hsub
  refine hsub.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
    fun α hα => ?_)
  exact (totalWeight_eq_scaled hM hα).symm

/-- Below any positive threshold the total weight is eventually
attained: the expansion regime is nonempty. -/
theorem eventually_totalWeight_lt (hM : M.PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ α in 𝓝[>] (0 : ℝ), totalWeight M α < ε := by
  have h := (tendsto_totalWeight_nhdsGT_zero hM).eventually
    (eventually_lt_nhds hε)
  exact h

/-! ## The logarithmic expansion and its truncation -/

/-- **The cluster expansion**: below unit weight the logarithm of the
mass splits into the zero mode and a convergent alternating series in
the residual, uniformly in the shift. -/
theorem hasSum_logMass_residual (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (hw : totalWeight M α < 1) (x : Fin d → ℝ) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1))
      (logMass M α x - Real.log (zeroMode M α)) := by
  have habs : |residual M α x| < 1 :=
    lt_of_le_of_lt (abs_residual_le_totalWeight hM hα x) hw
  have hneg : |(-residual M α x)| < 1 := by rwa [abs_neg]
  have hlog : Real.log (1 + residual M α x)
      = logMass M α x - Real.log (zeroMode M α) := by
    rw [logMass, gramMass_eq_zeroMode_mul hM hα x,
      Real.log_mul (zeroMode_pos hM hα).ne'
        (show (1 : ℝ) + residual M α x ≠ 0 by
          have := abs_lt.mp habs
          linarith)]
    ring
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hneg).neg
  rw [sub_neg_eq_add, neg_neg, hlog] at h
  refine h.congr_fun fun k => ?_
  rw [neg_pow]
  ring

/-- **The truncation estimate**: after `K` terms the error is bounded
by the total weight alone, uniformly in the shift. -/
theorem abs_logMass_sub_partialSum_le (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (hw : totalWeight M α < 1) (K : ℕ) (x : Fin d → ℝ) :
    |logMass M α x - Real.log (zeroMode M α)
        - ∑ k ∈ Finset.range K,
            (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1)|
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) := by
  have hle := abs_residual_le_totalWeight hM hα x
  have habs : |residual M α x| < 1 := lt_of_le_of_lt hle hw
  have hneg : |(-residual M α x)| < 1 := by rwa [abs_neg]
  have hlog : Real.log (1 + residual M α x)
      = logMass M α x - Real.log (zeroMode M α) := by
    rw [logMass, gramMass_eq_zeroMode_mul hM hα x,
      Real.log_mul (zeroMode_pos hM hα).ne'
        (show (1 : ℝ) + residual M α x ≠ 0 by
          have := abs_lt.mp habs
          linarith)]
    ring
  have h := Real.abs_log_sub_add_sum_range_le hneg K
  rw [sub_neg_eq_add, hlog] at h
  have hsum : ∑ k ∈ Finset.range K, (-residual M α x) ^ (k + 1) / (k + 1)
      = -∑ k ∈ Finset.range K,
          (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    ring
  rw [hsum, abs_neg] at h
  have hmono : |residual M α x| ^ (K + 1) / (1 - |residual M α x|)
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) := by
    have h1 : (0 : ℝ) < 1 - totalWeight M α := by linarith
    have h2 : (0 : ℝ) < 1 - |residual M α x| := by linarith
    have hw0 : 0 ≤ totalWeight M α := le_trans (abs_nonneg _) hle
    have hnum : |residual M α x| ^ (K + 1) ≤ totalWeight M α ^ (K + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hle _
    have hden : (1 : ℝ) - totalWeight M α ≤ 1 - |residual M α x| := by
      linarith
    calc |residual M α x| ^ (K + 1) / (1 - |residual M α x|)
        ≤ totalWeight M α ^ (K + 1) / (1 - |residual M α x|) :=
          div_le_div_of_nonneg_right hnum h2.le
      _ ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) :=
          div_le_div_of_nonneg_left (by positivity) h1 hden
  refine le_trans (le_of_eq ?_) (le_trans h hmono)
  congr 1
  ring

end Theaetetus
