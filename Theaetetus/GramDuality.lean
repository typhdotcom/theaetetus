import Theaetetus.Periodization
import Theaetetus.Defect

/-! # Higher-rank defect duality

The scale-indexed Boltzmann sum of a positive-definite Gram form,
`gramTheta M α = ∑_{k ∈ ℤᵈ} e^{−α·kᵀMk}`, reflects through the dual
Gram: Poisson summation for the Gaussian family
(`hasSum_gaussFourierCoeff_periodization_zero`) gives

    `gramTheta M⁻¹ (π²/α) = (α/π)^(d/2) · det(M)^(1/2) · gramTheta M α`

(`gramTheta_dual`), the rank-`d` form of `theta_duality_real` — at
`M = !![1]` the two coincide (`gramTheta_one_eq_theta`). The defect
of the Gram form on the divisibility lattice
(`gramDefect`, restricting to `defect` at rank one,
`gramDefect_one_eq_defect`) then satisfies the weight-zero duality

    `D_{M,s}(q,q′) = D_{M⁻¹,π²/(lcm²·s)}(q/gcd, q′/gcd)`

(`gramDefect_dual`): in the four-term alternating sum the
determinant weights cancel with multiplicity zero and the scale
weights cancel by `gcd·lcm = q·q′` — the symmetry survives at every
rank, with the dual Gram appearing. For coprime resolutions the
carrier pair is fixed and only the coupling reflects
(`gramDefect_dual_coprime`). -/

namespace Theaetetus

open Matrix

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- The scale-indexed Boltzmann sum of a Gram form:
`gramTheta M α = ∑_{k ∈ ℤᵈ} e^{−α·kᵀMk}`. -/
noncomputable def gramTheta (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ,
    Real.exp (-α * ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ))

/-- Summability of the Boltzmann weight at every positive scale. -/
theorem summable_gramTheta (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (-α * ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ))) := by
  refine (summable_exp_neg_quadForm (posDef_smul' hM hα)).congr fun k => ?_
  congr 1
  rw [neg_mul, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The Boltzmann sum is positive at every positive scale. -/
theorem gramTheta_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    0 < gramTheta M α := by
  have hle := (summable_gramTheta hM hα).sum_le_tsum {0}
    (fun k _ => (Real.exp_pos _).le)
  rw [Finset.sum_singleton] at hle
  exact lt_of_lt_of_le (Real.exp_pos _) hle

/-- At rank one with unit Gram, the Boltzmann sum is the scalar
theta function. -/
theorem gramTheta_one_eq_theta (α : ℝ) :
    gramTheta (!![1] : Matrix (Fin 1) (Fin 1) ℝ) α = theta α := by
  unfold gramTheta theta
  rw [← (Equiv.funUnique (Fin 1) ℤ).tsum_eq
    (fun n : ℤ => Real.exp (-α * (n : ℝ) ^ 2))]
  refine tsum_congr fun k => ?_
  have h : ∑ i, ∑ j, (!![1] : Matrix (Fin 1) (Fin 1) ℝ) i j
      * (k i : ℝ) * (k j : ℝ) = ((k default : ℤ) : ℝ) ^ 2 := by
    simp [Matrix.cons_val_fin_one]
    try ring
  rw [h]
  rfl

/-- **The Gram reflection**: Poisson summation for the Gaussian
family sends the Boltzmann sum of `M` at scale `α` to the Boltzmann
sum of the dual Gram `M⁻¹` at the reflected scale `π²/α`, with the
weight `(α/π)^(d/2)·det(M)^(1/2)`. At `d = 1`, `M = !![1]` this is
`theta_duality_real`. -/
theorem gramTheta_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    gramTheta M⁻¹ (Real.pi ^ 2 / α)
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2)
          * gramTheta M α := by
  have hπ := Real.pi_pos
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα hπ
  have hM' : ((α / Real.pi) • M).PosDef := posDef_smul' hM hc
  have hdet_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  -- the primal sum is the Gaussian periodization at the origin
  have hA : periodization ((α / Real.pi) • M) 0 = gramTheta M α := by
    unfold periodization gramTheta gaussian
    refine tsum_congr fun n => ?_
    congr 1
    rw [zero_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← quadForm_dotProduct]
    field_simp
  -- the inverse of the scaled Gram
  have hMinv : ((α / Real.pi) • M)⁻¹ = (Real.pi / α) • M⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_nonsing_inv _ hdet_unit,
      show α / Real.pi * (Real.pi / α) = 1 from by field_simp,
      one_smul]
  -- the Fourier coefficients are the dual Boltzmann weights
  have hcoeff : ∀ m : Fin d → ℤ,
      gaussFourierCoeff ((α / Real.pi) • M) m
        = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
          * Real.exp (-(Real.pi ^ 2 / α)
              * ∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) := by
    intro m
    unfold gaussFourierCoeff
    rw [Matrix.det_smul, Fintype.card_fin, hMinv]
    congr 1
    congr 1
    rw [neg_mul, neg_mul, neg_inj, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    field_simp
  -- Poisson at the origin, rewritten termwise
  set X : ℝ := (α / Real.pi) ^ d * M.det with hXdef
  have hXpos : (0 : ℝ) < X := mul_pos (pow_pos hc d) hM.det_pos
  have hkey : gramTheta M α
      = X⁻¹ ^ ((1 : ℝ) / 2) * gramTheta M⁻¹ (Real.pi ^ 2 / α) := by
    rw [← hA,
      ← (hasSum_gaussFourierCoeff_periodization_zero hM').tsum_eq,
      tsum_congr hcoeff, tsum_mul_left]
    rfl
  have hD : (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2)
      = X ^ ((1 : ℝ) / 2) := by
    rw [hXdef, Real.mul_rpow (by positivity) hM.det_pos.le]
    congr 1
    rw [← Real.rpow_natCast (α / Real.pi) d, ← Real.rpow_mul hc.le]
    congr 1
    ring
  have hprod : X ^ ((1 : ℝ) / 2) * X⁻¹ ^ ((1 : ℝ) / 2) = 1 := by
    rw [Real.inv_rpow hXpos.le,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos hXpos _).ne']
  calc gramTheta M⁻¹ (Real.pi ^ 2 / α)
      = 1 * gramTheta M⁻¹ (Real.pi ^ 2 / α) := (one_mul _).symm
    _ = X ^ ((1 : ℝ) / 2) * X⁻¹ ^ ((1 : ℝ) / 2)
          * gramTheta M⁻¹ (Real.pi ^ 2 / α) := by rw [hprod]
    _ = X ^ ((1 : ℝ) / 2)
          * (X⁻¹ ^ ((1 : ℝ) / 2) * gramTheta M⁻¹ (Real.pi ^ 2 / α)) := by
        ring
    _ = X ^ ((1 : ℝ) / 2) * gramTheta M α := by rw [← hkey]
    _ = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2)
          * gramTheta M α := by rw [hD]

/-- The reflection in logarithmic form: the weight splits into the
scale part and the determinant part. -/
private theorem log_gramTheta_dual (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) :
    Real.log (gramTheta M⁻¹ (Real.pi ^ 2 / α))
      = ((d : ℝ) / 2) * (Real.log α - Real.log Real.pi)
        + (1 / 2) * Real.log M.det
        + Real.log (gramTheta M α) := by
  have hπ := Real.pi_pos
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα hπ
  rw [gramTheta_dual hM hα,
    Real.log_mul
      (mul_pos (Real.rpow_pos_of_pos hc _)
        (Real.rpow_pos_of_pos hM.det_pos _)).ne'
      (gramTheta_pos hM hα).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne'
      (Real.rpow_pos_of_pos hM.det_pos _).ne',
    Real.log_rpow hc, Real.log_rpow hM.det_pos,
    Real.log_div hα.ne' Real.pi_ne_zero]

/-- The defect of a Gram form on the divisibility lattice: the
alternating sum of log-Boltzmann sums over the resolution rectangle
`{q, q′, gcd, lcm}` at scale `s`. At rank one with unit Gram this
is `defect` (`gramDefect_one_eq_defect`). -/
noncomputable def gramDefect (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (q q' : ℕ) : ℝ :=
  (Real.log (gramTheta M ((q : ℝ) ^ 2 * s))
      + Real.log (gramTheta M ((q' : ℝ) ^ 2 * s)))
    - (Real.log (gramTheta M ((Nat.gcd q q' : ℝ) ^ 2 * s))
      + Real.log (gramTheta M ((Nat.lcm q q' : ℝ) ^ 2 * s)))

/-- At rank one with unit Gram, the Gram defect is the defect. -/
theorem gramDefect_one_eq_defect (s : ℝ) (q q' : ℕ) :
    gramDefect (!![1] : Matrix (Fin 1) (Fin 1) ℝ) s q q'
      = defect s q q' := by
  unfold gramDefect defect
  simp only [gramTheta_one_eq_theta]

/-- **Higher-rank defect duality**: the defect of a Gram form at
scale `s` equals the defect of the dual Gram at the reflected scale
`π²/(lcm²·s)` and reduced resolutions. In the four-term alternating
sum the determinant weights of `gramTheta_dual` cancel with
multiplicity zero, and the scale weights cancel by
`gcd·lcm = q·q′`. -/
theorem gramDefect_dual (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    gramDefect M s q q'
      = gramDefect M⁻¹
          (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  have hπ := Real.pi_pos
  -- arithmetic of the reduction
  have hg : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hq
  have hgq : Nat.gcd q q' ∣ q := Nat.gcd_dvd_left q q'
  have hgq' : Nat.gcd q q' ∣ q' := Nat.gcd_dvd_right q q'
  have hco : Nat.Coprime (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
    Nat.coprime_div_gcd_div_gcd hg
  -- real casts
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hg
  have hlR : (0 : ℝ) < (Nat.lcm q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq.ne' hq'.ne')
  have hglqq : (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)
      = (q : ℝ) * (q' : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm q q'
  have haR : ((q / Nat.gcd q q' : ℕ) : ℝ)
      = (q : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq hgR.ne'
  have hbR : ((q' / Nat.gcd q q' : ℕ) : ℝ)
      = (q' : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq' hgR.ne'
  set t : ℝ := Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s) with htdef
  -- the involution permutes the four couplings
  have hswap : ∀ x y : ℝ, 0 < x → 0 < y
      → x * y = (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)
      → (x / (Nat.gcd q q' : ℝ)) ^ 2 * t
        = Real.pi ^ 2 / (y ^ 2 * s) := by
    intro x y hx hy hxy
    have hgl : (Nat.gcd q q' : ℝ) ^ 2 * ((Nat.lcm q q' : ℝ) ^ 2 * s)
        = x ^ 2 * (y ^ 2 * s) := by
      calc (Nat.gcd q q' : ℝ) ^ 2 * ((Nat.lcm q q' : ℝ) ^ 2 * s)
          = ((Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)) ^ 2 * s := by ring
        _ = (x * y) ^ 2 * s := by rw [hxy]
        _ = x ^ 2 * (y ^ 2 * s) := by ring
    rw [htdef, div_pow, div_mul_div_comm, hgl,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e1 : ((q / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((q' : ℝ) ^ 2 * s) := by
    rw [haR]
    exact hswap _ _ hqR hq'R (by linarith [hglqq])
  have e2 : ((q' / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((q : ℝ) ^ 2 * s) := by
    rw [hbR]
    exact hswap _ _ hq'R hqR (by linarith [hglqq])
  have e3 : ((1 : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s) := by
    rw [htdef]
    norm_num
  have e4 : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((Nat.gcd q q' : ℝ) ^ 2 * s) := by
    have hab : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ)
        = (Nat.lcm q q' : ℝ) / (Nat.gcd q q' : ℝ) := by
      rw [Nat.cast_mul, haR, hbR, div_mul_div_comm,
        div_eq_div_iff (by positivity) hgR.ne']
      linear_combination (-(Nat.gcd q q' : ℝ)) * hglqq
    rw [hab, htdef, div_pow, div_mul_div_comm,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- the four dual terms, reflected back
  have hda := log_gramTheta_dual hM
    (show (0 : ℝ) < (q' : ℝ) ^ 2 * s by positivity)
  have hdb := log_gramTheta_dual hM
    (show (0 : ℝ) < (q : ℝ) ^ 2 * s by positivity)
  have hdg := log_gramTheta_dual hM
    (show (0 : ℝ) < (Nat.lcm q q' : ℝ) ^ 2 * s by positivity)
  have hdl := log_gramTheta_dual hM
    (show (0 : ℝ) < (Nat.gcd q q' : ℝ) ^ 2 * s by positivity)
  -- the scale weights cancel by `gcd·lcm = q·q′`
  have hlogsum : Real.log ((q : ℝ) ^ 2 * s) + Real.log ((q' : ℝ) ^ 2 * s)
      = Real.log ((Nat.gcd q q' : ℝ) ^ 2 * s)
        + Real.log ((Nat.lcm q q' : ℝ) ^ 2 * s) := by
    rw [Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne']
    have hsq : Real.log ((q : ℝ) ^ 2) + Real.log ((q' : ℝ) ^ 2)
        = Real.log ((Nat.gcd q q' : ℝ) ^ 2)
          + Real.log ((Nat.lcm q q' : ℝ) ^ 2) := by
      rw [← Real.log_mul (by positivity) (by positivity),
        ← Real.log_mul (by positivity) (by positivity)]
      congr 1
      linear_combination
        (-((q : ℝ) * (q' : ℝ)
          + (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ))) * hglqq
    linarith
  unfold gramDefect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco,
    e1, e2, e3, e4, hda, hdb, hdg, hdl]
  linear_combination (-(d : ℝ) / 2) * hlogsum

/-- **Duality at coprime resolutions**: the carrier pair is fixed
and only the coupling reflects — through the dual Gram. -/
theorem gramDefect_dual_coprime (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hco : Nat.Coprime p q) :
    gramDefect M s p q
      = gramDefect M⁻¹
          (Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s)) p q := by
  have h := gramDefect_dual hM hs hp hq
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco] at h
  simpa [Nat.div_one, Nat.cast_mul] using h

end Theaetetus
