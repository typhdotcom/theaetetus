import Theaetetus.ReflectionFourier

/-! # Coset duality: the shifted defect reflects onto the twisted one

The shifted mass `gramMass M α y` is a periodized Gaussian, so
Poisson summation sends it to a sum over the dual lattice in which
the shift survives as a character: the **twisted Boltzmann sum**
`twistTheta M⁻¹ y (π²/α) = ∑_m cos(2π⟨m, y⟩)·e^{−(π²/α)·mᵀM⁻¹m}`,
with the same weight `(α/π)^(d/2)·det(M)^(1/2)` as the unshifted
reflection (`gramMass_dual`; at `y = 0` it is `gramTheta_dual`,
through `twistTheta_zero`). The twisted sum is therefore positive
(`twistTheta_pos`), and its logarithm differs from that of the
shifted mass by a weight affine in `log α`
(`log_twistTheta_dual`).

The annihilation law `fieldDefect_dual_of_log_reflect` erases that
weight, so the defect of the shifted mass reflects onto the defect
of the twisted sum, shift for shift (`shiftDefect_dual`).

Residue classes are shifts. The mass of the coset `c + 2ℤᵈ`,
`cosetMass M c β = ∑_k e^{−β·Q(c + 2k)}`, is the shifted mass at
quadrupled coupling and half shift (`cosetMass_eq_gramMass`), so
the classwise defect reflects onto the defect of the
`(−1)^⟨m,c⟩`-twisted dual sum at the scale `π²/(4·lcm²·s)`
(`cosetDefect_dual`): class by class, with no mixing between
classes. -/

namespace Theaetetus

open Matrix

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- The twisted Boltzmann sum: the Boltzmann sum of `M` with each
sector weighted by the character `cos(2π⟨m, y⟩)`. -/
noncomputable def twistTheta (M : Matrix (Fin d) (Fin d) ℝ)
    (y : Fin d → ℝ) (α : ℝ) : ℝ :=
  ∑' m : Fin d → ℤ,
    Real.cos (2 * Real.pi * dualPairing m y)
      * Real.exp (-α * ∑ i, ∑ j, M i j * (m i : ℝ) * (m j : ℝ))

/-- The untwisted case is the Boltzmann sum. -/
theorem twistTheta_zero (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) :
    twistTheta M 0 α = gramTheta M α := by
  unfold twistTheta gramTheta
  refine tsum_congr fun m => ?_
  simp [dualPairing]

/-- **The shifted reflection**: Poisson summation sends the shifted
mass of `M` at coupling `α` to the twisted Boltzmann sum of the dual
Gram at the reflected coupling, with the weight of `gramTheta_dual`. -/
theorem gramMass_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (y : Fin d → ℝ) :
    twistTheta M⁻¹ y (Real.pi ^ 2 / α)
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2)
          * gramMass M α y := by
  have hπ := Real.pi_pos
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα hπ
  set X : ℝ := (α / Real.pi) ^ d * M.det with hXdef
  have hXpos : (0 : ℝ) < X := mul_pos (pow_pos hc d) hM.det_pos
  have hkey : gramMass M α y = X⁻¹ ^ ((1 : ℝ) / 2) * twistTheta M⁻¹ y (Real.pi ^ 2 / α) := by
    rw [← (hasSum_massFourier_cos hM hα y).tsum_eq, twistTheta, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [massFourierCoeff_eq hM hα m]
    ring
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
  rw [hD, hkey, ← mul_assoc, hprod, one_mul]

/-- The twisted Boltzmann sum of the dual Gram is positive at every
positive coupling: it is a positive multiple of a shifted mass. -/
theorem twistTheta_pos (hM : M.PosDef) {β : ℝ} (hβ : 0 < β)
    (y : Fin d → ℝ) : 0 < twistTheta M⁻¹ y β := by
  have hπ := Real.pi_pos
  have hα : 0 < Real.pi ^ 2 / β := by positivity
  have h := gramMass_dual hM hα y
  rw [show Real.pi ^ 2 / (Real.pi ^ 2 / β) = β by field_simp] at h
  rw [h]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (div_pos hα hπ) _)
    (Real.rpow_pos_of_pos hM.det_pos _)) (gramMass_pos hM hα y)

/-- The shifted reflection in logarithmic form: the weight is affine
in `log α`. -/
theorem log_twistTheta_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (y : Fin d → ℝ) :
    Real.log (twistTheta M⁻¹ y (Real.pi ^ 2 / α))
      = ((d : ℝ) / 2) * (Real.log α - Real.log Real.pi)
        + (1 / 2) * Real.log M.det
        + Real.log (gramMass M α y) := by
  have hπ := Real.pi_pos
  have hc : (0 : ℝ) < α / Real.pi := div_pos hα hπ
  rw [gramMass_dual hM hα y,
    Real.log_mul
      (mul_pos (Real.rpow_pos_of_pos hc _)
        (Real.rpow_pos_of_pos hM.det_pos _)).ne'
      (gramMass_pos hM hα y).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne'
      (Real.rpow_pos_of_pos hM.det_pos _).ne',
    Real.log_rpow hc, Real.log_rpow hM.det_pos,
    Real.log_div hα.ne' Real.pi_ne_zero]

/-- **The shifted defect reflects onto the twisted defect**: the
defect of the shifted mass at scale `s` is the defect of the twisted
dual Boltzmann sum, at the same shift, at the reflected scale and
reduced resolutions. -/
theorem shiftDefect_dual (hM : M.PosDef) (y : Fin d → ℝ) {s : ℝ}
    (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect (fun α => gramMass M α y) s q q'
      = fieldDefect (twistTheta M⁻¹ y)
          (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  fieldDefect_dual_of_log_reflect
    (a := (d : ℝ) / 2)
    (b := (1 / 2) * Real.log M.det - (d : ℝ) / 2 * Real.log Real.pi)
    (fun α hα => by rw [log_twistTheta_dual hM hα y]; ring) hs hq hq'

/-! ## Residue classes -/

/-- The Boltzmann mass of the coset `c + 2ℤᵈ`. -/
noncomputable def cosetMass (M : Matrix (Fin d) (Fin d) ℝ)
    (c : Fin d → ℤ) (β : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ,
    Real.exp (-β * ((fun i => (c i : ℝ) + 2 * (k i : ℝ))
      ⬝ᵥ M.mulVec (fun i => (c i : ℝ) + 2 * (k i : ℝ))))

/-- The half shift of a residue representative. -/
noncomputable def halfShift (c : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (c i : ℝ) / 2

/-- A coset mass is the shifted mass at quadrupled coupling and half
shift. -/
theorem cosetMass_eq_gramMass (M : Matrix (Fin d) (Fin d) ℝ)
    (c : Fin d → ℤ) (β : ℝ) :
    cosetMass M c β = gramMass M (4 * β) (halfShift c) := by
  unfold cosetMass gramMass
  refine tsum_congr fun k => ?_
  have hv : (fun i => (c i : ℝ) + 2 * (k i : ℝ))
      = (2 : ℝ) • (halfShift c + fun i => (k i : ℝ)) := by
    funext i
    simp only [halfShift, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  congr 1
  ring

/-- The `(−1)^⟨m,c⟩` character of the half shift. -/
theorem cos_dualPairing_halfShift (m c : Fin d → ℤ) :
    Real.cos (2 * Real.pi * dualPairing m (halfShift c))
      = (-1 : ℝ) ^ (∑ i, m i * c i) := by
  have h : 2 * Real.pi * dualPairing m (halfShift c)
      = ((∑ i, m i * c i : ℤ) : ℝ) * Real.pi := by
    simp only [dualPairing, halfShift]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h, Real.cos_int_mul_pi]

/-- **Classwise duality**: the defect of the coset mass of `c + 2ℤᵈ`
reflects onto the defect of the `(−1)^⟨m,c⟩`-twisted dual
Boltzmann sum at scale `π²/(4·lcm²·s)`, class by class. -/
theorem cosetDefect_dual (hM : M.PosDef) (c : Fin d → ℤ) {s : ℝ}
    (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect (cosetMass M c) s q q'
      = fieldDefect (twistTheta M⁻¹ (halfShift c))
          (Real.pi ^ 2 / (4 * (Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  have h4 : fieldDefect (cosetMass M c) s q q'
      = fieldDefect (fun α => gramMass M α (halfShift c)) (4 * s) q q' := by
    simp only [fieldDefect, cosetMass_eq_gramMass]
    ring_nf
  rw [h4, shiftDefect_dual hM _ (by positivity) hq hq']
  congr 2
  ring

end Theaetetus
