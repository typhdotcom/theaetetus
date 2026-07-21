import Theaetetus.CrossRatio
import Theaetetus.ThetaBounds

/-! # Rank two: the defect on the theta graph

The first rank-two witness (M4): on the theta graph `K₂,₃` — the
smallest carrier of rank two — the defect at the incomparable pair
`(2, 3)` is strictly negative (`thetaGraph_towerDefect_neg`).

The carrier's cycle Gram is `!![4, 2; 2, 4]` (two four-edge cycles
sharing a two-edge path), so the harmonic energy is the **hexagonal
form** `(a² − ab + b²)/3` and the scaled partition functions are the
rank-two theta sum `hexTheta` (`thetaGraph_classScaledPartFn`).

The estimates:

* **Row factorization** (`hexTheta_le`): completing the square
  splits the hexagonal sum into rows; each shifted row is dominated
  by the unshifted one through the **periodization bound**
  (`periodization_le_periodization_zero`, the `≤` form of the
  strict Fourier-positivity theorem), giving
  `hexTheta s ≤ θ(s/3)·θ(s/4)` — numerically near-tight.
* **Shell lower bound** (`hexTheta_ge`): the six norm-1 vectors and
  the six norm-3 vectors give
  `1 + 6e^(−s/3) + 6e^(−s) ≤ hexTheta s`.
* The comparison closes by the scalar estimate kit and rational
  arithmetic — the same three exponential constants as the
  rank-one witness, plus decimal bounds on `e⁻¹`. -/

namespace Theaetetus

open scoped BigOperators
open Matrix

/-! ## The periodization bound, `≤` form -/

/-- The periodized Gaussian is maximized at lattice points, weak
form: strict off the integer shifts
(`periodization_lt_periodization_zero`), equality on them
(`periodization_add_int`). -/
theorem periodization_le_periodization_zero {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (x : Fin d → ℝ) :
    periodization M x ≤ periodization M 0 := by
  by_cases hx : ∃ i₀ : Fin d, ∀ k : ℤ, x i₀ ≠ (k : ℝ)
  · obtain ⟨i₀, hi⟩ := hx
    exact (periodization_lt_periodization_zero hM hi).le
  · push_neg at hx
    choose m hm using hx
    have hxm : x = (0 : Fin d → ℝ) + fun i => ((m i : ℤ) : ℝ) := by
      funext i
      simp [hm i]
    rw [hxm, periodization_add_int]

/-! ## The shifted-row bound -/

private lemma dot_fin_one (a : ℝ) (y : Fin 1 → ℝ) :
    y ⬝ᵥ (!![a]).mulVec y = a * y 0 ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Matrix.cons_val_fin_one]
  ring

/-- The rank-one periodization at shift `c` is the shifted theta
sum. -/
private lemma periodization_fin_one (α : ℝ) (c : ℝ) :
    periodization !![α / Real.pi] (fun _ => c)
      = ∑' k : ℤ, Real.exp (-(α * ((k : ℝ) + c) ^ 2)) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold periodization gaussian
  rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℤ).symm]
  refine tsum_congr fun k => ?_
  rw [dot_fin_one]
  have hy : ((fun _ : Fin 1 => c) + fun i =>
      ((((Equiv.funUnique (Fin 1) ℤ).symm k) i : ℤ) : ℝ)) 0
      = c + (k : ℝ) := by
    simp
  rw [hy]
  congr 1
  field_simp
  ring

/-- **The shifted-row bound**: a real-shifted theta sum is dominated
by the unshifted one — the workhorse the rank-two factorization
feeds each row through. -/
theorem tsum_exp_shift_le {α : ℝ} (hα : 0 < α) (c : ℝ) :
    ∑' k : ℤ, Real.exp (-(α * ((k : ℝ) + c) ^ 2)) ≤ theta α := by
  have hM : (!![α / Real.pi] : Matrix (Fin 1) (Fin 1) ℝ).PosDef :=
    (QuadraticAction.ofScalar (α / Real.pi) (by positivity)).Q_posDef
  have h := periodization_le_periodization_zero hM (fun _ => c)
  rw [periodization_fin_one α c] at h
  refine h.trans_eq ?_
  rw [show (0 : Fin 1 → ℝ) = (fun _ : Fin 1 => (0 : ℝ)) from rfl,
    periodization_fin_one α 0]
  refine tsum_congr fun k => ?_
  congr 1
  ring

/-! ## The hexagonal theta sum -/

/-- The rank-two theta sum of the hexagonal form `(a² − ab + b²)/3`
— the harmonic energy of the theta graph. -/
noncomputable def hexTheta (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ,
    Real.exp (-(s * (((p.1 : ℝ) ^ 2 - p.1 * p.2 + p.2 ^ 2) / 3)))

set_option maxHeartbeats 1000000 in
theorem summable_hexTheta {s : ℝ} (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-(s * (((p.1 : ℝ) ^ 2 - p.1 * p.2 + p.2 ^ 2) / 3)))) := by
  have h6 : (0 : ℝ) < s / 6 := by positivity
  have hF : Summable (fun k : ℤ => ‖Real.exp (-(s / 6) * (k : ℝ) ^ 2)‖) :=
    (summable_theta (s / 6) h6).congr fun k => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmaj : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(s / 6) * (p.1 : ℝ) ^ 2)
        * Real.exp (-(s / 6) * (p.2 : ℝ) ^ 2)) :=
    summable_mul_of_summable_norm hF hF
  refine hmaj.of_nonneg_of_le (fun p => (Real.exp_pos _).le) fun p => ?_
  dsimp only
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith [mul_nonneg hs.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

/-! ## The theta graph's scaled partition functions are `hexTheta` -/

/-- The cycle Gram of the theta graph's lattice basis: two four-edge
cycles sharing a two-edge path. -/
private lemma gramOf_thetaCycles :
    gramOf (fun i e => ((thetaCyclesZ i e : ℤ) : ℝ)) = !![4, 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramOf, dotProduct, Fin.sum_univ_six, thetaCyclesZ] <;>
    norm_num

/-- The inverse Gram: the hexagonal form's matrix. -/
private lemma inv_gram_theta :
    (!![(4 : ℝ), 2; 2, 4])⁻¹ = !![1 / 3, -(1 / 6); -(1 / 6), 1 / 3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- **The theta graph's scaled partition functions are the
hexagonal theta sum**: the rank-two carrier with energy
`(a² − ab + b²)/3` sums to `hexTheta s`. -/
theorem thetaGraph_classScaledPartFn (s : ℝ) :
    thetaGraph.classScaledPartFn s = hexTheta s := by
  have hE : ∀ p : ℤ × ℤ,
      thetaGraph.harmonicEnergy
          ((thetaGraph.latticeQuotEquiv thetaLatticeBasis).symm
            ((piFinTwoEquiv (fun _ => ℤ)).symm p))
        = ((p.1 : ℝ) ^ 2 - p.1 * p.2 + p.2 ^ 2) / 3 := by
    intro p
    rw [← thetaGraph.basisGramData_energy_latticeQuot thetaLatticeBasis,
      LinearEquiv.apply_symm_apply]
    show ∑ i, ∑ j,
        (gramOf (thetaGraph.cyclesR thetaLatticeBasis))⁻¹ i j
          * ((((piFinTwoEquiv (fun _ => ℤ)).symm p) i : ℝ))
          * ((((piFinTwoEquiv (fun _ => ℤ)).symm p) j : ℝ))
      = ((p.1 : ℝ) ^ 2 - p.1 * p.2 + p.2 ^ 2) / 3
    rw [cyclesR_thetaLatticeBasis, gramOf_thetaCycles, inv_gram_theta,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
      show (((piFinTwoEquiv (fun _ => ℤ)).symm p) 0) = p.1 from rfl,
      show (((piFinTwoEquiv (fun _ => ℤ)).symm p) 1) = p.2 from rfl]
    norm_num
    all_goals ring
  show (∑' κ : (Fin 6 → ℤ) ⧸ LinearMap.range (thetaGraph.gradLin ℤ),
    Real.exp (-(s * thetaGraph.harmonicEnergy κ))) = _
  rw [← Equiv.tsum_eq
    ((piFinTwoEquiv (fun _ => ℤ)).symm.trans
      (thetaGraph.latticeQuotEquiv thetaLatticeBasis).symm.toEquiv)
    (fun κ => Real.exp (-(s * thetaGraph.harmonicEnergy κ)))]
  refine tsum_congr fun p => ?_
  rw [show ((piFinTwoEquiv (fun _ => ℤ)).symm.trans
      (thetaGraph.latticeQuotEquiv thetaLatticeBasis).symm.toEquiv) p
      = (thetaGraph.latticeQuotEquiv thetaLatticeBasis).symm
        ((piFinTwoEquiv (fun _ => ℤ)).symm p) from rfl,
    hE p]

/-! ## The two estimates -/

/-- **Row factorization**: completing the square in the hexagonal
form and dominating each shifted row by the unshifted theta sum. -/
theorem hexTheta_le {s : ℝ} (hs : 0 < s) :
    hexTheta s ≤ theta (s / 3) * theta (s / 4) := by
  have hs3 : (0 : ℝ) < s / 3 := by positivity
  have hs4 : (0 : ℝ) < s / 4 := by positivity
  -- per-term split
  have hterm : ∀ p : ℤ × ℤ,
      Real.exp (-(s * (((p.1 : ℝ) ^ 2 - p.1 * p.2 + p.2 ^ 2) / 3)))
        = Real.exp (-(s / 3 * ((p.1 : ℝ) + -((p.2 : ℝ)) / 2) ^ 2))
          * Real.exp (-(s / 4 * (p.2 : ℝ) ^ 2)) := by
    intro p
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(s / 3 * ((p.1 : ℝ) + -((p.2 : ℝ)) / 2) ^ 2))
        * Real.exp (-(s / 4 * (p.2 : ℝ) ^ 2))) :=
    (summable_hexTheta hs).congr hterm
  -- swap to sum rows over the second coordinate
  have hrowsum : ∀ b : ℤ, Summable (fun a : ℤ =>
      Real.exp (-(s / 3 * ((a : ℝ) + -((b : ℝ)) / 2) ^ 2))
        * Real.exp (-(s / 4 * (b : ℝ) ^ 2))) := fun b =>
    (summable_exp_shift (s / 3) hs3 (-((b : ℝ)) / 2)).mul_right _
  have hswap : hexTheta s = ∑' b : ℤ, ∑' a : ℤ,
      Real.exp (-(s / 3 * ((a : ℝ) + -((b : ℝ)) / 2) ^ 2))
        * Real.exp (-(s / 4 * (b : ℝ) ^ 2)) := by
    unfold hexTheta
    rw [tsum_congr hterm, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
    exact ((Equiv.prodComm ℤ ℤ).summable_iff.mpr hsum).tsum_prod'
      fun b => hrowsum b
  rw [hswap]
  -- pull the row factor out and bound each shifted row
  have hrow : ∀ b : ℤ,
      (∑' a : ℤ, Real.exp (-(s / 3 * ((a : ℝ) + -((b : ℝ)) / 2) ^ 2))
        * Real.exp (-(s / 4 * (b : ℝ) ^ 2)))
      ≤ theta (s / 3) * Real.exp (-(s / 4 * (b : ℝ) ^ 2)) := by
    intro b
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (tsum_exp_shift_le hs3 (-((b : ℝ)) / 2))
      (Real.exp_pos _).le
  have hmaj : Summable (fun b : ℤ =>
      theta (s / 3) * Real.exp (-(s / 4 * (b : ℝ) ^ 2))) := by
    refine ((summable_theta (s / 4) hs4).mul_left (theta (s / 3))).congr
      fun b => ?_
    rw [show -(s / 4) * (b : ℝ) ^ 2 = -(s / 4 * (b : ℝ) ^ 2) from by ring]
  have hleft : Summable (fun b : ℤ =>
      ∑' a : ℤ, Real.exp (-(s / 3 * ((a : ℝ) + -((b : ℝ)) / 2) ^ 2))
        * Real.exp (-(s / 4 * (b : ℝ) ^ 2))) := by
    refine Summable.of_nonneg_of_le
      (fun b => tsum_nonneg fun a => by positivity) hrow hmaj
  calc (∑' b : ℤ, ∑' a : ℤ,
        Real.exp (-(s / 3 * ((a : ℝ) + -((b : ℝ)) / 2) ^ 2))
          * Real.exp (-(s / 4 * (b : ℝ) ^ 2)))
      ≤ ∑' b : ℤ, theta (s / 3) * Real.exp (-(s / 4 * (b : ℝ) ^ 2)) :=
        hleft.tsum_le_tsum hrow hmaj
    _ = theta (s / 3) * ∑' b : ℤ, Real.exp (-(s / 4 * (b : ℝ) ^ 2)) :=
        tsum_mul_left
    _ = theta (s / 3) * theta (s / 4) := by
        congr 1
        refine tsum_congr fun b => ?_
        congr 1
        ring

/-- **Shell lower bound**: the six norm-1 vectors and the six norm-3
vectors of the hexagonal form. -/
theorem hexTheta_ge {s : ℝ} (hs : 0 < s) :
    1 + 6 * Real.exp (-(s / 3)) + 6 * Real.exp (-s) ≤ hexTheta s := by
  have hsum := summable_hexTheta hs
  have hle := hsum.sum_le_tsum
    ({((0 : ℤ), (0 : ℤ)), (1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1),
      (1, -1), (-1, 1), (2, 1), (-2, -1), (1, 2), (-1, -2)} : Finset (ℤ × ℤ))
    (fun p _ => (Real.exp_pos _).le)
  refine le_trans (le_of_eq ?_) hle
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num
  ring_nf

/-- The vacuum term alone: `1 ≤ hexTheta`. -/
theorem one_le_hexTheta {s : ℝ} (hs : 0 < s) : 1 ≤ hexTheta s := by
  have h := hexTheta_ge hs
  nlinarith [Real.exp_pos (-(s / 3)), Real.exp_pos (-s)]

/-! ## The rank-two witness -/

/-- **THE RANK-TWO WITNESS** (M4): on the theta graph — the smallest
carrier of rank two — the defect at the incomparable pair `(2, 3)`
is strictly negative. The hexagonal comparison
`hexTheta 4 · hexTheta 9 < hexTheta 1 · hexTheta 36` closes through
the row factorization, the shell lower bound, and the same three
exponential constants as the rank-one witness. -/
theorem thetaGraph_towerDefect_neg : thetaGraph.towerDefect 2 3 < 0 := by
  -- the four theta values, in hexagonal form
  rw [thetaGraph.crossRatio_law 2 3,
    show Nat.gcd 2 3 = 1 from by decide,
    show Nat.lcm 2 3 = 6 from by decide,
    show (((2 : ℕ) : ℝ)) ^ 2 = 4 from by norm_num,
    show (((3 : ℕ) : ℝ)) ^ 2 = 9 from by norm_num,
    show (((1 : ℕ) : ℝ)) ^ 2 = 1 from by norm_num,
    show (((6 : ℕ) : ℝ)) ^ 2 = 36 from by norm_num,
    thetaGraph_classScaledPartFn, thetaGraph_classScaledPartFn,
    thetaGraph_classScaledPartFn, thetaGraph_classScaledPartFn]
  -- scalar numeric bounds
  obtain ⟨hc, ha, hb⟩ := exp_numeric_bounds
  have ht43 : theta (4 / 3) < 127 / 73 := by
    have hle := theta_le (4 / 3) (by norm_num)
    have hfrac : Real.exp (-(4 / 3)) / (1 - Real.exp (-(4 / 3))) < 27 / 73 := by
      rw [div_lt_iff₀ (by nlinarith [Real.exp_pos (-(4 / 3))])]
      linarith
    linarith
  have ht1 : theta 1 < 1784 / 1000 := by
    have h := theta_le_two_mode (α := 1) (by norm_num)
    rw [show (4 : ℝ) * 1 = 4 from by norm_num,
      show (2 : ℝ) * 1 = 2 from by norm_num] at h
    have h1 := exp_neg_one_lt
    have h2 := exp_neg_two_lt
    have h4 := exp_neg_four_lt
    have hden : (0 : ℝ) < 1 - Real.exp (-2) := by
      nlinarith [Real.exp_pos (-2)]
    have hfrac : Real.exp (-4) / (1 - Real.exp (-2)) < 22 / 1000 := by
      rw [div_lt_iff₀ hden]
      linarith
    linarith
  have ht3 : theta 3 < 21 / 19 := by
    have hle := theta_le 3 (by norm_num)
    have hfrac : Real.exp (-3) / (1 - Real.exp (-3)) < 1 / 19 := by
      rw [div_lt_iff₀ (by nlinarith [Real.exp_pos (-3)])]
      linarith
    linarith
  have ht94 : theta (9 / 4) < 1318 / 1000 := by
    have hmono := theta_anti (α := 2) (by norm_num) (by norm_num : (2 : ℝ) ≤ 9 / 4)
    have hle := theta_le 2 (by norm_num)
    have h2 := exp_neg_two_lt
    have hden : (0 : ℝ) < 1 - Real.exp (-2) := by
      nlinarith [Real.exp_pos (-2)]
    have hfrac : Real.exp (-2) / (1 - Real.exp (-2)) < 159 / 1000 := by
      rw [div_lt_iff₀ hden]
      linarith
    linarith
  -- hexagonal bounds at the four scales
  have h4 : hexTheta 4 ≤ theta (4 / 3) * theta 1 := by
    have h := hexTheta_le (s := 4) (by norm_num)
    rwa [show (4 : ℝ) / 4 = 1 from by norm_num] at h
  have h9 : hexTheta 9 ≤ theta 3 * theta (9 / 4) := by
    have h := hexTheta_le (s := 9) (by norm_num)
    rwa [show (9 : ℝ) / 3 = 3 from by norm_num] at h
  have h1ge : (184 : ℝ) / 25 < hexTheta 1 := by
    have h := hexTheta_ge (s := 1) (by norm_num)
    rw [show (1 : ℝ) / 3 = 1 / 3 from rfl] at h
    have he13 := hc
    have he1 := exp_neg_one_gt
    linarith
  have h36ge : (1 : ℝ) ≤ hexTheta 36 := one_le_hexTheta (by norm_num)
  -- positivity
  have hp4 : (0 : ℝ) < hexTheta 4 :=
    lt_of_lt_of_le one_pos (one_le_hexTheta (by norm_num))
  have hp9 : (0 : ℝ) < hexTheta 9 :=
    lt_of_lt_of_le one_pos (one_le_hexTheta (by norm_num))
  have hp1 : (0 : ℝ) < hexTheta 1 :=
    lt_of_lt_of_le one_pos (one_le_hexTheta (by norm_num))
  have hp36 : (0 : ℝ) < hexTheta 36 :=
    lt_of_lt_of_le one_pos (one_le_hexTheta (by norm_num))
  have ht43p : (0 : ℝ) < theta (4 / 3) := theta_pos _ (by norm_num)
  have ht1p : (0 : ℝ) < theta 1 := theta_pos _ (by norm_num)
  have ht3p : (0 : ℝ) < theta 3 := theta_pos _ (by norm_num)
  have ht94p : (0 : ℝ) < theta (9 / 4) := theta_pos _ (by norm_num)
  -- the product comparison
  have hprod : hexTheta 4 * hexTheta 9 < hexTheta 1 * hexTheta 36 := by
    have hL1 : hexTheta 4 * hexTheta 9
        ≤ (theta (4 / 3) * theta 1) * (theta 3 * theta (9 / 4)) :=
      mul_le_mul h4 h9 hp9.le (by positivity)
    have hL2 : (theta (4 / 3) * theta 1) * (theta 3 * theta (9 / 4))
        < (127 / 73 * (1784 / 1000)) * (21 / 19 * (1318 / 1000)) := by
      have hA : theta (4 / 3) * theta 1 < 127 / 73 * (1784 / 1000) :=
        mul_lt_mul'' ht43 ht1 ht43p.le ht1p.le
      have hB : theta 3 * theta (9 / 4) < 21 / 19 * (1318 / 1000) :=
        mul_lt_mul'' ht3 ht94 ht3p.le ht94p.le
      exact mul_lt_mul'' hA hB (by positivity) (by positivity)
    have hnum : (127 / 73 * (1784 / 1000) : ℝ) * (21 / 19 * (1318 / 1000))
        < 184 / 25 := by norm_num
    have hR : (184 : ℝ) / 25 ≤ hexTheta 1 * hexTheta 36 := by
      calc (184 : ℝ) / 25 ≤ hexTheta 1 := h1ge.le
        _ = hexTheta 1 * 1 := (mul_one _).symm
        _ ≤ hexTheta 1 * hexTheta 36 :=
            mul_le_mul_of_nonneg_left h36ge hp1.le
    linarith
  -- close through the logarithm
  have hlog := Real.log_lt_log (mul_pos hp4 hp9) hprod
  rw [Real.log_mul hp4.ne' hp9.ne', Real.log_mul hp1.ne' hp36.ne'] at hlog
  linarith

end Theaetetus
