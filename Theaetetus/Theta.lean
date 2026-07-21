-- ported from Meno/QuadraticAction.lean (the scalar layer;
-- Meno's `scalarPartFn` takes this project's name `theta`)
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! # θ: the scalar theta function

`theta α = ∑' k : ℤ, exp(-α k²)` — the rank-one Boltzmann sum, the
analytic carrier of the whole rank-one program (PROGRAM.md, Q1–Q2).

Contents, all ported from the quarry:

* summability (`summable_theta`);
* the theta identification `theta_eq_jacobiTheta` — `theta` *is*
  the Jacobi theta function at `τ = iα/π` — and through it the
  **duality** `theta (π²/α) = √(α/π) · theta α` (Jacobi
  transformation, the small-`s` tool for Q1);
* the estimate kit: `theta_gt_one`, the symmetric split
  `theta_sub_one_eq`, the first-mode lower bound `theta_ge`, and
  the geometric tail upper bound `theta_le` — the large-`s` tools,
  and the engine of the witness (M2). -/

namespace Theaetetus

open UpperHalfPlane Complex

/-- The scalar theta function `θ(α) = ∑' k : ℤ, exp(-α k²)`. -/
noncomputable def theta (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)

/-! ## Summability -/

private lemma summable_theta_nat (α : ℝ) (hα : 0 < α) :
    Summable (fun i : ℕ => Real.exp (-α * (↑i : ℝ) ^ 2)) := by
  have hle : ∀ i : ℕ, (↑i : ℝ) ≤ (↑i : ℝ) ^ 2 := by
    intro i; rcases i with _ | i
    · simp
    · nlinarith [sq_nonneg ((↑(i + 1) : ℝ) - 1),
        show (1 : ℝ) ≤ ↑(i + 1) from by exact_mod_cast Nat.succ_pos i]
  exact (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hα)
    (f := fun i => (↑i : ℝ) ^ 2) hle).congr fun i => by congr 1

theorem summable_theta (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) :=
  .of_nat_of_neg (summable_theta_nat α hα)
    ((summable_theta_nat α hα).congr fun i => by push_cast; congr 1; ring)

/-! ## The theta identification and the duality -/

/-- The upper-half-plane parameter at coupling `α`: `τ(α) = iα/π`.
Public because it is the canonical dictionary entry between coupling
and modular parameter: `θ(α) = ϑ₃(τ(α))`. -/
noncomputable def quadTau (α : ℝ) : ℂ :=
  Complex.I * ↑α / ↑Real.pi

private lemma quad_tau_im_pos (α : ℝ) (hα : 0 < α) : (quadTau α).im > 0 := by
  unfold quadTau
  rw [mul_div_assoc, ← Complex.ofReal_div, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, one_mul, zero_add]
  exact div_pos hα Real.pi_pos

private noncomputable def quadUHP (α : ℝ) (hα : 0 < α) : UpperHalfPlane :=
  ⟨quadTau α, quad_tau_im_pos α hα⟩

private lemma quad_theta_exponent (α : ℝ) (k : ℤ) :
    ↑Real.pi * Complex.I * (↑k : ℂ) ^ 2 * quadTau α =
    ↑(-α * (k : ℝ) ^ 2) := by
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- **Theta identification**: the scalar theta function *is* the
Jacobi theta function at `τ = iα/π`. The single analytic source for
every duality statement downstream. -/
theorem theta_eq_jacobiTheta (α : ℝ) :
    (↑(theta α) : ℂ) = jacobiTheta (quadTau α) := by
  simp only [theta, jacobiTheta]
  rw [Complex.ofReal_tsum]
  congr 1; ext k
  rw [quad_theta_exponent α k, ← Complex.ofReal_exp]

private theorem quad_S_transform (α : ℝ) (hα : 0 < α) :
    (↑(ModularGroup.S • quadUHP α hα) : ℂ) = quadTau (Real.pi ^ 2 / α) := by
  have h : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [modular_S_smul, coe_mk, h]
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hα0 : (↑α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  push_cast; field_simp; exact Complex.I_sq.symm

private theorem quad_prefactor (α : ℝ) (hα : 0 < α) :
    -Complex.I * (↑(quadUHP α hα) : ℂ) = ↑(α / Real.pi : ℝ) := by
  have : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [this]; simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- **The duality** (Jacobi transformation) at the theta level:
`θ(π²/α) = √(α/π) · θ(α)`. -/
theorem theta_duality (α : ℝ) (hα : 0 < α) :
    (↑(theta (Real.pi ^ 2 / α)) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑(theta α) := by
  have hτ : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [theta_eq_jacobiTheta, theta_eq_jacobiTheta,
      show quadTau (Real.pi ^ 2 / α) = ↑(ModularGroup.S • quadUHP α hα) from
        (quad_S_transform α hα).symm,
      jacobiTheta_S_smul, quad_prefactor α hα, hτ]

/-- Real form of the duality: `θ(π²/α) = (α/π)^(1/2) · θ(α)` with
the real `rpow`. -/
theorem theta_duality_real (α : ℝ) (hα : 0 < α) :
    theta (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * theta α := by
  have h := theta_duality α hα
  have hnn : (0 : ℝ) ≤ α / Real.pi := le_of_lt (div_pos hα Real.pi_pos)
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hnn]
  convert h using 2
  push_cast; ring

/-! ## The estimate kit -/

/-- The theta function strictly exceeds 1: the vacuum sector
contributes 1, and the `k = 1` sector contributes `exp(-α) > 0`. -/
theorem theta_gt_one (α : ℝ) (hα : 0 < α) : 1 < theta α := by
  have hsm := summable_theta α hα
  have hle : ({0, 1} : Finset ℤ).sum (fun k => Real.exp (-α * (k : ℝ) ^ 2)) ≤
      theta α := by
    show _ ≤ ∑' k, _
    exact hsm.sum_le_tsum {0, 1} (fun k _ => le_of_lt (Real.exp_pos _))
  simp at hle
  linarith [Real.exp_pos (-α)]

/-- The theta function is strictly positive. -/
theorem theta_pos (α : ℝ) (hα : 0 < α) : 0 < theta α :=
  zero_lt_one.trans (theta_gt_one α hα)

/-- Shifted-mode summability: the positive modes of the theta sum
converge. -/
theorem summable_exp_sq_shift (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) := by
  have h := (summable_nat_add_iff 1).mpr (summable_theta_nat α hα)
  exact h.congr fun k => by push_cast; rfl

/-- Symmetric split: the theta function minus its vacuum term
equals twice the sum over positive modes. The ℤ-sum over `k²`
collapses to the ℕ-sum over `(k+1)²` doubled (by evenness) plus the
`k = 0` term. -/
theorem theta_sub_one_eq (α : ℝ) (hα : 0 < α) :
    theta α - 1 = 2 * ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
  set S : ℝ := ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) with hS_def
  have hshift : Summable (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) :=
    summable_exp_sq_shift α hα
  have hSum_S : HasSum (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) S :=
    hshift.hasSum
  have hf₁ : HasSum
      (fun n : ℕ => Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast
    rfl
  have hf₂ : HasSum
      (fun n : ℕ => Real.exp (-α * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast
    ring_nf
  have hZ : HasSum (fun k : ℤ => Real.exp (-α * ((k : ℤ) : ℝ) ^ 2))
      (S + Real.exp (-α * (((0 : ℤ) : ℝ)) ^ 2) + S) :=
    HasSum.of_add_one_of_neg_add_one hf₁ hf₂
  have hZ_val : theta α = S + 1 + S := by
    have h := hZ.tsum_eq
    have h0 : Real.exp (-α * (((0 : ℤ) : ℝ)) ^ 2) = 1 := by simp
    rw [h0] at h
    show ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2) = S + 1 + S
    convert h using 1
  rw [hZ_val]
  ring

/-- Per-mode geometric domination:
`exp(−α(k+1)²) ≤ exp(−α)·exp(−α)^k`. -/
theorem exp_sq_shift_le_geo (α : ℝ) (hα : 0 < α) (k : ℕ) :
    Real.exp (-α * ((k : ℝ) + 1) ^ 2) ≤ Real.exp (-α) * Real.exp (-α) ^ k := by
  rw [show Real.exp (-α) * Real.exp (-α) ^ k
      = Real.exp (-α * ((k : ℝ) + 1)) from by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf]
  refine Real.exp_le_exp.mpr ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1) hk]

/-- First-mode lower bound: `1 + 2·exp(−α) ≤ θ(α)`. -/
theorem theta_ge (α : ℝ) (hα : 0 < α) :
    1 + 2 * Real.exp (-α) ≤ theta α := by
  have h := theta_sub_one_eq α hα
  have hfirst : Real.exp (-α)
      ≤ ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
    have hle := (summable_exp_sq_shift α hα).sum_le_tsum {0}
      (fun j _ => (Real.exp_pos _).le)
    rw [Finset.sum_singleton] at hle
    calc Real.exp (-α) = Real.exp (-α * (((0 : ℕ) : ℝ) + 1) ^ 2) := by
          norm_num
      _ ≤ _ := hle
  linarith

/-- Geometric tail upper bound:
`θ(α) ≤ 1 + 2·exp(−α)/(1−exp(−α))`. -/
theorem theta_le (α : ℝ) (hα : 0 < α) :
    theta α ≤ 1 + 2 * (Real.exp (-α) / (1 - Real.exp (-α))) := by
  have h := theta_sub_one_eq α hα
  have hexp_pos : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have hlt : Real.exp (-α) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeo : Summable (fun k : ℕ => Real.exp (-α) ^ k) :=
    summable_geometric_of_lt_one hexp_pos.le hlt
  have hbound : ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      ≤ Real.exp (-α) / (1 - Real.exp (-α)) := by
    calc ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2)
        ≤ ∑' k : ℕ, Real.exp (-α) * Real.exp (-α) ^ k :=
          (summable_exp_sq_shift α hα).tsum_le_tsum
            (exp_sq_shift_le_geo α hα) (hgeo.mul_left _)
      _ = Real.exp (-α) * ∑' k : ℕ, Real.exp (-α) ^ k :=
          hgeo.tsum_mul_left (Real.exp (-α))
      _ = Real.exp (-α) * (1 - Real.exp (-α))⁻¹ := by
          rw [tsum_geometric_of_lt_one hexp_pos.le hlt]
      _ = Real.exp (-α) / (1 - Real.exp (-α)) := by
          rw [div_eq_mul_inv]
  linarith

end Theaetetus
