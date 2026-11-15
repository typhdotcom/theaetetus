import Theaetetus.LatticeDuality
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Higher-rank thermodynamic curvature and its duality

The Gram Boltzmann sum `gramTheta M α = ∑_k e^{−α·E(k)}`,
`E(k) = kᵀMk` (`gramEnergy`), differentiates termwise in the
coupling: each energy moment `∑_k E^m e^{−αE}` (`gramMoment`)
differentiates to minus the next (`hasDerivAt_gramMoment`), the
derivatives dominated on `(α/2, ∞)` by the moment majorant at
`α/2` (`summable_gramMoment`). So the Gibbs mean energy
(`gramMeanEnergy`) is minus the logarithmic derivative of the
partition function (`hasDerivAt_log_gramTheta`) and the Gibbs
variance (`gramVariance`) is minus the derivative of the mean
energy (`hasDerivAt_gramMeanEnergy`). For a form of positive rank
the variance is strictly positive (`gramVariance_pos`), so the
mean energy is strictly decreasing (`gramMeanEnergy_strictAntiOn`).

Differentiating the Gram reflection `log_gramTheta_dual` once gives
the mean-energy functional equation

    `α·⟨E⟩_M(α) + (π²/α)·⟨E⟩_{M⁻¹}(π²/α) = d/2`

(`gramMeanEnergy_dual`), the rank-`d` form of `theta_logDeriv_dual`;
differentiating again, the curvature
`α²·Var_M(α) − α·⟨E⟩_M(α)` (`gramCurvature`) reflects exactly to the
curvature of the dual Gram at the reflected coupling
(`gramCurvature_dual`). The curvature is the second derivative of
`u ↦ log Z(e^u)` at `u = log α` (`logCurvature`,
`logCurvature_gramTheta`), and `log(π²/α) = 2·log π − log α`, so the
reflection reads `H_M″(u) = H_{M⁻¹}″(2·log π − u)`.

Strict positivity of the curvature on `β ≥ π` for a form and its
dual therefore gives it at every positive coupling
(`gramCurvature_pos_of_ge_pi`); intrinsically, for a lattice action
and its dual lattice (`QuadLatticeAction.logCurvature_dual`,
`QuadLatticeAction.logCurvature_pos_of_ge_pi`). -/

namespace Theaetetus

open Matrix Filter Topology

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- The energy of an integral vector under a Gram form: `kᵀMk`. -/
def gramEnergy (M : Matrix (Fin d) (Fin d) ℝ) (k : Fin d → ℤ) : ℝ :=
  ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)

private theorem gramEnergy_eq_dotProduct (M : Matrix (Fin d) (Fin d) ℝ) (k : Fin d → ℤ) :
    gramEnergy M k
      = star (fun i => (k i : ℝ)) ⬝ᵥ M.mulVec (fun i => (k i : ℝ)) := by
  rw [star_trivial]
  exact quadForm_dotProduct M (fun i => (k i : ℝ))

theorem gramEnergy_nonneg (hM : M.PosDef) (k : Fin d → ℤ) : 0 ≤ gramEnergy M k := by
  rw [gramEnergy_eq_dotProduct]
  exact hM.posSemidef.dotProduct_mulVec_nonneg _

theorem gramEnergy_pos (hM : M.PosDef) {k : Fin d → ℤ} (hk : k ≠ 0) :
    0 < gramEnergy M k := by
  rw [gramEnergy_eq_dotProduct]
  refine hM.dotProduct_mulVec_pos fun h => hk (funext fun i => ?_)
  simpa using congrFun h i

@[simp] theorem gramEnergy_zero (M : Matrix (Fin d) (Fin d) ℝ) : gramEnergy M 0 = 0 := by
  simp [gramEnergy]

/-- The `m`-th energy moment of the Gram Boltzmann weight. -/
noncomputable def gramMoment (M : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) (α : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ, gramEnergy M k ^ m * Real.exp (-α * gramEnergy M k)

theorem gramMoment_zero (M : Matrix (Fin d) (Fin d) ℝ) : gramMoment M 0 = gramTheta M := by
  funext α
  simp only [gramMoment, pow_zero, one_mul]
  rfl

/-- **Moment summability**: every energy moment converges at positive
coupling, dominated by the Boltzmann sum at half the coupling. -/
theorem summable_gramMoment (hM : M.PosDef) (m : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable fun k : Fin d → ℤ => gramEnergy M k ^ m * Real.exp (-α * gramEnergy M k) := by
  have hhalf : 0 < α / 2 := by linarith
  have hw : Summable fun k : Fin d → ℤ => Real.exp (-(α / 2) * gramEnergy M k) :=
    summable_gramTheta hM hhalf
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (gramEnergy_nonneg hM k) _) (Real.exp_pos _).le)
    (fun k => ?_) (hw.mul_left ((m.factorial : ℝ) * (2 / α) ^ m))
  have hE := gramEnergy_nonneg hM k
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h1 := Real.pow_div_factorial_le_exp (hx := mul_nonneg hhalf.le hE) (n := m)
  rw [div_le_iff₀ hfac, mul_pow] at h1
  have h2 : gramEnergy M k ^ m
      ≤ (m.factorial : ℝ) * (2 / α) ^ m * Real.exp (α / 2 * gramEnergy M k) := by
    have hsplit : gramEnergy M k ^ m
        = (2 / α) ^ m * ((α / 2) ^ m * gramEnergy M k ^ m) := by
      rw [← mul_assoc, ← mul_pow, show 2 / α * (α / 2) = 1 by field_simp, one_pow, one_mul]
    rw [hsplit]
    calc (2 / α) ^ m * ((α / 2) ^ m * gramEnergy M k ^ m)
        ≤ (2 / α) ^ m * (Real.exp (α / 2 * gramEnergy M k) * m.factorial) := by gcongr
      _ = _ := by ring
  calc gramEnergy M k ^ m * Real.exp (-α * gramEnergy M k)
      ≤ ((m.factorial : ℝ) * (2 / α) ^ m * Real.exp (α / 2 * gramEnergy M k))
          * Real.exp (-α * gramEnergy M k) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) * (2 / α) ^ m * Real.exp (-(α / 2) * gramEnergy M k) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **Termwise differentiation**: each energy moment differentiates
in the coupling to minus the next. -/
theorem hasDerivAt_gramMoment (hM : M.PosDef) (m : ℕ) {α : ℝ} (hα : 0 < α) :
    HasDerivAt (gramMoment M m) (-gramMoment M (m + 1) α) α := by
  have hhalf : (0 : ℝ) < α / 2 := by linarith
  have hmem : α ∈ Set.Ioi (α / 2) := Set.mem_Ioi.mpr (by linarith)
  have hg : ∀ (k : Fin d → ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      HasDerivAt (fun x : ℝ => gramEnergy M k ^ m * Real.exp (-x * gramEnergy M k))
        (gramEnergy M k ^ m * (Real.exp (-y * gramEnergy M k) * (-1 * gramEnergy M k))) y :=
    fun k y _ => ((((hasDerivAt_id y).neg).mul_const _).exp).const_mul _
  have hg' : ∀ (k : Fin d → ℤ) (y : ℝ), y ∈ Set.Ioi (α / 2) →
      ‖gramEnergy M k ^ m * (Real.exp (-y * gramEnergy M k) * (-1 * gramEnergy M k))‖
        ≤ gramEnergy M k ^ (m + 1) * Real.exp (-(α / 2) * gramEnergy M k) := by
    intro k y hy
    have hE := gramEnergy_nonneg hM k
    have hmono : Real.exp (-y * gramEnergy M k) ≤ Real.exp (-(α / 2) * gramEnergy M k) :=
      Real.exp_le_exp.mpr (by nlinarith [Set.mem_Ioi.mp hy])
    rw [Real.norm_eq_abs,
      show gramEnergy M k ^ m * (Real.exp (-y * gramEnergy M k) * (-1 * gramEnergy M k))
        = -(gramEnergy M k ^ (m + 1) * Real.exp (-y * gramEnergy M k)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (pow_nonneg hE _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left hmono (pow_nonneg hE _)
  have key := hasDerivAt_tsum_of_isPreconnected
    (summable_gramMoment hM (m + 1) hhalf) isOpen_Ioi isPreconnected_Ioi
    hg hg' hmem (summable_gramMoment hM m hα) hmem
  have hval : (∑' k : Fin d → ℤ,
      gramEnergy M k ^ m * (Real.exp (-α * gramEnergy M k) * (-1 * gramEnergy M k)))
        = -gramMoment M (m + 1) α := by
    unfold gramMoment
    rw [← tsum_neg]
    exact tsum_congr fun k => by ring
  rw [hval] at key
  exact key

theorem hasDerivAt_gramTheta (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasDerivAt (gramTheta M) (-gramMoment M 1 α) α := by
  rw [← gramMoment_zero]
  exact hasDerivAt_gramMoment hM 0 hα

/-- The Gibbs mean energy of the Gram form at coupling `α`. -/
noncomputable def gramMeanEnergy (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  gramMoment M 1 α / gramTheta M α

/-- The Gibbs variance of the energy at coupling `α`. -/
noncomputable def gramVariance (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  gramMoment M 2 α / gramTheta M α - gramMeanEnergy M α ^ 2

/-- The thermodynamic curvature `α²·Var(E) − α·⟨E⟩` at coupling `α`. -/
noncomputable def gramCurvature (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : ℝ :=
  α ^ 2 * gramVariance M α - α * gramMeanEnergy M α

/-- **The mean energy is a logarithmic derivative**:
`(log Z)′(α) = −⟨E⟩(α)`. -/
theorem hasDerivAt_log_gramTheta (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasDerivAt (fun β => Real.log (gramTheta M β)) (-gramMeanEnergy M α) α := by
  have h := (hasDerivAt_gramTheta hM hα).log (gramTheta_pos hM hα).ne'
  rwa [neg_div] at h

/-- **Fluctuation–dissipation**: the derivative of the mean energy is
minus the variance. -/
theorem hasDerivAt_gramMeanEnergy (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasDerivAt (gramMeanEnergy M) (-gramVariance M α) α := by
  have hG := (gramTheta_pos hM hα).ne'
  have h1 : HasDerivAt (gramMoment M 1) (-gramMoment M 2 α) α := hasDerivAt_gramMoment hM 1 hα
  refine (h1.div (hasDerivAt_gramTheta hM hα) hG).congr_deriv ?_
  unfold gramVariance gramMeanEnergy
  field_simp
  ring

/-- The variance is the Gibbs average of the squared deviation from
the mean. -/
private theorem hasSum_sq_dev (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasSum (fun k : Fin d → ℤ =>
        (gramEnergy M k - gramMeanEnergy M α) ^ 2 * Real.exp (-α * gramEnergy M k))
      (gramVariance M α * gramTheta M α) := by
  set e := gramMeanEnergy M α
  have hw : Summable fun k : Fin d → ℤ => Real.exp (-α * gramEnergy M k) :=
    summable_gramTheta hM hα
  have h := (((summable_gramMoment hM 2 hα).hasSum).sub
    (((summable_gramMoment hM 1 hα).hasSum).mul_left (2 * e))).add (hw.hasSum.mul_left (e ^ 2))
  have hG := (gramTheta_pos hM hα).ne'
  convert h using 1
  · funext k
    ring
  · change gramVariance M α * gramTheta M α
      = gramMoment M 2 α - 2 * e * gramMoment M 1 α + e ^ 2 * gramTheta M α
    simp only [gramVariance, e, gramMeanEnergy]
    field_simp
    ring

/-- **Strict fluctuation**: for a form of positive rank the energy
variance is strictly positive — the zero vector sits at energy `0`,
strictly below the mean. -/
theorem gramVariance_pos (hM : M.PosDef) (hd : 0 < d) {α : ℝ} (hα : 0 < α) :
    0 < gramVariance M α := by
  have hG := gramTheta_pos hM hα
  set k₀ : Fin d → ℤ := Pi.single ⟨0, hd⟩ 1
  have hk₀ : k₀ ≠ 0 := fun h => by
    have := congrFun h ⟨0, hd⟩
    simp [k₀] at this
  have hm1 : 0 < gramMoment M 1 α :=
    (summable_gramMoment hM 1 hα).tsum_pos
      (fun k => mul_nonneg (pow_nonneg (gramEnergy_nonneg hM k) _) (Real.exp_pos _).le) k₀
      (mul_pos (pow_pos (gramEnergy_pos hM hk₀) _) (Real.exp_pos _))
  have he : 0 < gramMeanEnergy M α := div_pos hm1 hG
  have hS := hasSum_sq_dev hM hα
  have hpos : 0 < gramVariance M α * gramTheta M α := by
    rw [← hS.tsum_eq]
    refine hS.summable.tsum_pos (fun k => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) 0 ?_
    simp only [gramEnergy_zero, mul_zero, Real.exp_zero, mul_one, zero_sub, neg_sq]
    positivity
  exact pos_of_mul_pos_left hpos hG.le

/-- **Strict dissipation**: for a form of positive rank the mean
energy is strictly decreasing in the coupling. -/
theorem gramMeanEnergy_strictAntiOn (hM : M.PosDef) (hd : 0 < d) :
    StrictAntiOn (gramMeanEnergy M) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hasDerivAt_gramMeanEnergy hM (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt)
    fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_gramMeanEnergy hM (Set.mem_Ioi.mp hx)).deriv]
  exact neg_neg_of_pos (gramVariance_pos hM hd (Set.mem_Ioi.mp hx))

private theorem hasDerivAt_reflect {α : ℝ} (hα : 0 < α) :
    HasDerivAt (fun β : ℝ => Real.pi ^ 2 / β) (-(Real.pi ^ 2) / α ^ 2) α := by
  have h := (hasDerivAt_inv hα.ne').const_mul (Real.pi ^ 2)
  simp only [← div_eq_mul_inv] at h
  refine h.congr_deriv ?_
  field_simp

/-- **The mean-energy functional equation**: the Gram reflection,
differentiated once in the coupling —
`α·⟨E⟩_M(α) + (π²/α)·⟨E⟩_{M⁻¹}(π²/α) = d/2`. At rank one this is
`theta_logDeriv_dual`. -/
theorem gramMeanEnergy_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    α * gramMeanEnergy M α + Real.pi ^ 2 / α * gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α)
      = (d : ℝ) / 2 := by
  have hα0 := hα.ne'
  have hγ : 0 < Real.pi ^ 2 / α := div_pos (pow_pos Real.pi_pos 2) hα
  have hL : HasDerivAt (fun β => Real.log (gramTheta M⁻¹ (Real.pi ^ 2 / β)))
      (-gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α) * (-(Real.pi ^ 2) / α ^ 2)) α :=
    (hasDerivAt_log_gramTheta (posDef_inv hM) hγ).comp α (hasDerivAt_reflect hα)
  have hR : HasDerivAt
      (fun β => (d : ℝ) / 2 * (Real.log β - Real.log Real.pi) + 1 / 2 * Real.log M.det
        + Real.log (gramTheta M β))
      ((d : ℝ) / 2 * α⁻¹ + -gramMeanEnergy M α) α :=
    ((((Real.hasDerivAt_log hα0).sub_const _).const_mul _).add_const _).add
      (hasDerivAt_log_gramTheta hM hα)
  have heq : (fun β => Real.log (gramTheta M⁻¹ (Real.pi ^ 2 / β))) =ᶠ[𝓝 α]
      (fun β => (d : ℝ) / 2 * (Real.log β - Real.log Real.pi) + 1 / 2 * Real.log M.det
        + Real.log (gramTheta M β)) := by
    filter_upwards [eventually_gt_nhds hα] with β hβ
    exact log_gramTheta_dual hM hβ
  have hu := (hL.congr_of_eventuallyEq heq.symm).unique hR
  have h1 : Real.pi ^ 2 / α * gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α)
      = α * (-gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α) * (-(Real.pi ^ 2) / α ^ 2)) := by
    field_simp
  have h2 : (d : ℝ) / 2 = α * ((d : ℝ) / 2 * α⁻¹) := by
    field_simp
  rw [h1, h2, hu]
  ring

/-- **Curvature reflection**: the thermodynamic curvature of `M` at
`α` equals that of the dual Gram `M⁻¹` at `π²/α` — the functional
equation `gramMeanEnergy_dual`, differentiated once more. -/
theorem gramCurvature_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    gramCurvature M α = gramCurvature M⁻¹ (Real.pi ^ 2 / α) := by
  have hα0 := hα.ne'
  have hγ : 0 < Real.pi ^ 2 / α := div_pos (pow_pos Real.pi_pos 2) hα
  have hE : HasDerivAt (fun β => β * gramMeanEnergy M β)
      (1 * gramMeanEnergy M α + α * -gramVariance M α) α :=
    (hasDerivAt_id α).mul (hasDerivAt_gramMeanEnergy hM hα)
  have hEs : HasDerivAt (fun β => gramMeanEnergy M⁻¹ (Real.pi ^ 2 / β))
      (-gramVariance M⁻¹ (Real.pi ^ 2 / α) * (-(Real.pi ^ 2) / α ^ 2)) α :=
    (hasDerivAt_gramMeanEnergy (posDef_inv hM) hγ).comp α (hasDerivAt_reflect hα)
  have hF := hE.add ((hasDerivAt_reflect hα).mul hEs)
  have hconst : (fun β => β * gramMeanEnergy M β
        + Real.pi ^ 2 / β * gramMeanEnergy M⁻¹ (Real.pi ^ 2 / β)) =ᶠ[𝓝 α]
      fun _ => (d : ℝ) / 2 := by
    filter_upwards [eventually_gt_nhds hα] with β hβ
    exact gramMeanEnergy_dual hM hβ
  have hu := hF.unique ((hasDerivAt_const α ((d : ℝ) / 2)).congr_of_eventuallyEq hconst)
  unfold gramCurvature
  set e := gramMeanEnergy M α
  set v := gramVariance M α
  set e' := gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α)
  set v' := gramVariance M⁻¹ (Real.pi ^ 2 / α)
  have key : (α ^ 2 * v - α * e) - ((Real.pi ^ 2 / α) ^ 2 * v' - Real.pi ^ 2 / α * e')
      = -α * (1 * e + α * -v
        + (-(Real.pi ^ 2) / α ^ 2 * e' + Real.pi ^ 2 / α * (-v' * (-(Real.pi ^ 2) / α ^ 2)))) := by
    field_simp
    ring
  rw [hu, mul_zero] at key
  linarith

/-- The curvature of `u ↦ log Z(e^u)` at `u = log β`. -/
noncomputable def logCurvature (Z : ℝ → ℝ) (β : ℝ) : ℝ :=
  deriv (deriv fun u => Real.log (Z (Real.exp u))) (Real.log β)

private theorem hasDerivAt_log_gramTheta_exp (hM : M.PosDef) (u : ℝ) :
    HasDerivAt (fun u => Real.log (gramTheta M (Real.exp u)))
      (-(Real.exp u * gramMeanEnergy M (Real.exp u))) u := by
  refine ((hasDerivAt_log_gramTheta hM (Real.exp_pos u)).comp u
    (Real.hasDerivAt_exp u)).congr_deriv ?_
  ring

/-- **The curvature is the second logarithmic derivative**: the
second derivative of `u ↦ log gramTheta M (e^u)` at `log β` is
`β²·Var(E) − β·⟨E⟩`. -/
theorem logCurvature_gramTheta (hM : M.PosDef) {β : ℝ} (hβ : 0 < β) :
    logCurvature (gramTheta M) β = gramCurvature M β := by
  have hd : deriv (fun u => Real.log (gramTheta M (Real.exp u)))
      = fun u => -(Real.exp u * gramMeanEnergy M (Real.exp u)) :=
    funext fun u => (hasDerivAt_log_gramTheta_exp hM u).deriv
  have h2 : HasDerivAt (fun u => -(Real.exp u * gramMeanEnergy M (Real.exp u)))
      (gramCurvature M (Real.exp (Real.log β))) (Real.log β) := by
    have h := ((Real.hasDerivAt_exp (Real.log β)).mul
      ((hasDerivAt_gramMeanEnergy hM (Real.exp_pos (Real.log β))).comp (Real.log β)
        (Real.hasDerivAt_exp (Real.log β)))).neg
    refine h.congr_deriv ?_
    unfold gramCurvature
    simp only [Function.comp_apply]
    ring
  unfold logCurvature
  rw [hd, h2.deriv, Real.exp_log hβ]

/-- **The reduction to large coupling**: if the strict curvature
inequality `β·⟨E⟩ < β²·Var(E)` holds for a form and for its dual on
`β ≥ π`, it holds for the form at every positive coupling. -/
theorem gramCurvature_pos_of_ge_pi (hM : M.PosDef)
    (h : ∀ β, Real.pi ≤ β → β * gramMeanEnergy M β < β ^ 2 * gramVariance M β)
    (h' : ∀ β, Real.pi ≤ β → β * gramMeanEnergy M⁻¹ β < β ^ 2 * gramVariance M⁻¹ β)
    {β : ℝ} (hβ : 0 < β) : β * gramMeanEnergy M β < β ^ 2 * gramVariance M β := by
  rcases le_or_gt Real.pi β with hπβ | hβπ
  · exact h β hπβ
  · have hγ : Real.pi ≤ Real.pi ^ 2 / β := by
      rw [le_div_iff₀ hβ]
      nlinarith [Real.pi_pos]
    have h1 := h' _ hγ
    have hc := gramCurvature_dual hM hβ
    unfold gramCurvature at hc
    linarith

namespace QuadLatticeAction

variable (Q : QuadLatticeAction.{u})

/-- Every Gram chart computes the curvature of the lattice action. -/
theorem logCurvature_eq_gramCurvature {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    {β : ℝ} (hβ : 0 < β) :
    logCurvature Q.scaledPartFn β = gramCurvature (Q.gram b) β := by
  rw [show Q.scaledPartFn = gramTheta (Q.gram b) from funext (Q.scaledPartFn_eq_gramTheta b)]
  exact logCurvature_gramTheta (Q.gram_posDef b) hβ

/-- **Intrinsic curvature reflection**: the curvature of a lattice
action at `β` is the curvature of its dual lattice at `π²/β`. -/
theorem logCurvature_dual {β : ℝ} (hβ : 0 < β) :
    logCurvature Q.scaledPartFn β = logCurvature Q.dual.scaledPartFn (Real.pi ^ 2 / β) := by
  rw [Q.logCurvature_eq_gramCurvature (Module.finBasis ℤ Q.Λ) hβ,
    Q.dual.logCurvature_eq_gramCurvature (Module.finBasis ℤ Q.Λ).dualBasis
      (div_pos (pow_pos Real.pi_pos 2) hβ),
    dual_gram]
  exact gramCurvature_dual (Q.gram_posDef _) hβ

/-- **Intrinsic reduction to large coupling**: strict curvature of a
lattice action and of its dual on `β ≥ π` gives strict curvature of
the lattice action at every positive coupling. -/
theorem logCurvature_pos_of_ge_pi
    (h : ∀ β, Real.pi ≤ β → 0 < logCurvature Q.scaledPartFn β)
    (h' : ∀ β, Real.pi ≤ β → 0 < logCurvature Q.dual.scaledPartFn β)
    {β : ℝ} (hβ : 0 < β) : 0 < logCurvature Q.scaledPartFn β := by
  rcases le_or_gt Real.pi β with hπβ | hβπ
  · exact h β hπβ
  · rw [Q.logCurvature_dual hβ]
    refine h' _ ?_
    rw [le_div_iff₀ hβ]
    nlinarith [Real.pi_pos]

end QuadLatticeAction

end Theaetetus
