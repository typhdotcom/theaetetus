import Theaetetus.GramDuality
import Theaetetus.PartitionTower

/-! # The scale asymptotics of a Gram Boltzmann sum

Two limits bracket the Boltzmann sum of a positive-definite Gram
form. At large coupling only the origin survives: the sum saturates
at `1` (`tendsto_gramTheta_atTop`), which is the generic tower
saturation applied to the tower of the form itself — the integer
lattice graded by the quadratic form, with the origin as its modal
sector (`gramTower`, `gramTower_Z`).

At small scale the sum diverges, and the reflection says exactly
how fast. Read at the dual form, the sum at a small scale is the
dual sum at a large one carrying the scale power and the
determinant weight (`gramTheta_eq_dual`), so saturation at the far
end fixes the near end:

    (s/π)^(d/2)·gramTheta(M, s) → det(M)^(−1/2)   as s → 0⁺

(`tendsto_gramTheta_nhdsGT_zero`). The normalization is universal in
the rank, so it cancels between two forms of the same rank: their
Boltzmann sums compare at small scale by the square root of the
reciprocal determinant ratio (`tendsto_gramTheta_ratio`), which is
the ratio of covolumes. -/

namespace Theaetetus

open Filter Topology Matrix

variable {d : ℕ} {M N : Matrix (Fin d) (Fin d) ℝ}

/-! ## The tower of a Gram form -/

private theorem gram_quad_pos (hM : M.PosDef) {k : Fin d → ℤ} (hk : k ≠ 0) :
    0 < ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ) := by
  rw [quadForm_dotProduct]
  have hne : (fun i => ((k i : ℤ) : ℝ)) ≠ 0 := by
    intro h
    refine hk (funext fun i => ?_)
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    exact_mod_cast hi
  have hstar : star (fun i => ((k i : ℤ) : ℝ)) = fun i => ((k i : ℤ) : ℝ) :=
    funext fun i => star_trivial _
  have hpos := (posDef_iff_dotProduct_mulVec.mp hM).2 hne
  rwa [hstar] at hpos

/-- The partition tower of a positive-definite Gram form: the
integer lattice graded by the quadratic form, with the origin as its
modal sector. -/
noncomputable def gramTower (hM : M.PosDef) : PartitionTower.{0} where
  Λ := Fin d → ℤ
  E := fun k => ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
  E_zero := ⟨0, by simp⟩
  E_nonneg := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp
    · exact (gram_quad_pos hM hk).le
  summable := summable_exp_neg_quadForm hM
  modal := 0
  E_modal := by simp
  E_pos := fun k hk => gram_quad_pos hM hk

theorem gramTower_Z (hM : M.PosDef) (β : ℝ) :
    (gramTower hM).Z β = gramTheta M β := by
  show (∑' k : Fin d → ℤ,
      Real.exp (-(β * ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ))))
    = ∑' k : Fin d → ℤ,
        Real.exp (-β * ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ))
  exact tsum_congr fun k => by rw [neg_mul]

/-! ## Saturation at large coupling -/

/-- **Saturation**: at large coupling only the origin survives, so
the Boltzmann sum of a positive-definite Gram form tends to `1`. -/
theorem tendsto_gramTheta_atTop (hM : M.PosDef) :
    Tendsto (gramTheta M) atTop (𝓝 1) :=
  (gramTower hM).tendsto_Z_atTop.congr (gramTower_Z hM)

/-! ## The small-scale asymptotic -/

/-- The reflection read at the dual form: the Boltzmann sum at a
small scale is the dual sum at a large one, carrying the scale power
and the determinant weight. -/
theorem gramTheta_eq_dual (hM : M.PosDef) {s : ℝ} (hs : 0 < s) :
    gramTheta M s
      = (Real.pi / s) ^ ((d : ℝ) / 2) * (M.det⁻¹) ^ ((1 : ℝ) / 2)
        * gramTheta M⁻¹ (Real.pi ^ 2 / s) := by
  have hinv : M⁻¹.PosDef := posDef_inv hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hα : (0 : ℝ) < Real.pi ^ 2 / s := by positivity
  have h := gramTheta_dual hinv hα
  rw [show Real.pi ^ 2 / (Real.pi ^ 2 / s) = s by field_simp,
    Matrix.nonsing_inv_nonsing_inv M hunit,
    show Real.pi ^ 2 / s / Real.pi = Real.pi / s by field_simp,
    show M⁻¹.det = M.det⁻¹ by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']] at h
  exact h

private theorem tendsto_pi_sq_div :
    Tendsto (fun s : ℝ => Real.pi ^ 2 / s) (𝓝[>] (0 : ℝ)) atTop := by
  refine (Filter.Tendsto.const_mul_atTop (r := Real.pi ^ 2) (by positivity)
    tendsto_inv_nhdsGT_zero).congr fun s => ?_
  rw [div_eq_mul_inv]

/-- **The determinant-normalized small-scale asymptotic**: the
Boltzmann sum of a positive-definite Gram form, normalized by the
scale power, converges to the inverse square root of the determinant
as the scale falls to zero. -/
theorem tendsto_gramTheta_nhdsGT_zero (hM : M.PosDef) :
    Tendsto (fun s : ℝ => (s / Real.pi) ^ ((d : ℝ) / 2) * gramTheta M s)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.det ^ (-(1 : ℝ) / 2))) := by
  have hinv : M⁻¹.PosDef := posDef_inv hM
  have hsat := (tendsto_gramTheta_atTop hinv).comp tendsto_pi_sq_div
  have hD : (M.det⁻¹) ^ ((1 : ℝ) / 2) = M.det ^ (-(1 : ℝ) / 2) := by
    rw [Real.inv_rpow hM.det_pos.le, neg_div, Real.rpow_neg hM.det_pos.le]
  have hlim : Tendsto (fun s : ℝ =>
      M.det ^ (-(1 : ℝ) / 2) * gramTheta M⁻¹ (Real.pi ^ 2 / s))
      (𝓝[>] (0 : ℝ)) (𝓝 (M.det ^ (-(1 : ℝ) / 2))) := by
    have h := (tendsto_const_nhds (x := M.det ^ (-(1 : ℝ) / 2))
      (f := 𝓝[>] (0 : ℝ))).mul hsat
    rw [mul_one] at h
    exact h
  refine hlim.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
    fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  have hcancel : (s / Real.pi) ^ ((d : ℝ) / 2)
      * (Real.pi / s) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show s / Real.pi * (Real.pi / s) = 1 by field_simp, Real.one_rpow]
  rw [gramTheta_eq_dual hM hs', ← hD]
  linear_combination (-((M.det⁻¹) ^ ((1 : ℝ) / 2)
    * gramTheta M⁻¹ (Real.pi ^ 2 / s))) * hcancel

/-- **The ratio limit**: at small scale the Boltzmann sums of two
positive-definite Gram forms of the same rank compare by the square
root of the reciprocal determinant ratio — the scale powers
cancel. -/
theorem tendsto_gramTheta_ratio (hM : M.PosDef) (hN : N.PosDef) :
    Tendsto (fun s : ℝ => gramTheta M s / gramTheta N s) (𝓝[>] (0 : ℝ))
      (𝓝 ((N.det / M.det) ^ ((1 : ℝ) / 2))) := by
  have hden : N.det ^ (-(1 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hN.det_pos _).ne'
  have hdiv := (tendsto_gramTheta_nhdsGT_zero hM).div
    (tendsto_gramTheta_nhdsGT_zero hN) hden
  have hval : M.det ^ (-(1 : ℝ) / 2) / N.det ^ (-(1 : ℝ) / 2)
      = (N.det / M.det) ^ ((1 : ℝ) / 2) := by
    rw [Real.div_rpow hN.det_pos.le hM.det_pos.le, neg_div,
      Real.rpow_neg hM.det_pos.le,
      Real.rpow_neg hN.det_pos.le]
    field_simp
  rw [hval] at hdiv
  refine hdiv.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
    fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  have hne : (s / Real.pi) ^ ((d : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  exact mul_div_mul_left _ _ hne

end Theaetetus
