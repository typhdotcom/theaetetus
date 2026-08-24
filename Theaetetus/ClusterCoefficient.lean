import Theaetetus.ClusterExpansion

/-! # Coefficients of the cluster expansion

The cluster normalization writes the logarithmic mass as the zero
mode plus a convergent series in the residual. This module reads that
series at the level of Fourier coefficients.

The tools are elementary. A nontrivial character integrates to zero,
because translating the integral by a point where the character is
not `1` multiplies it by a scalar other than `1`
(`integral_mFourier`), so the characters are orthogonal under the
coefficient functional (`mFourierCoeff_mFourier`). A function
presented by an absolutely summable character series therefore has
those very coefficients (`HasCharSum`,
`HasCharSum.mFourierCoeff_eq`); the interchange is legitimate because
the characters are unimodular and the measure is a probability
measure. Multiplying two such series and regrouping by the sum of the
indices gives the convolution (`convolve`, `HasCharSum.mul`), and
iterating gives the convolution powers (`convPow`, `HasCharSum.pow`).

The residual is such a series, with its zero mode deleted
(`modeCoeff`, `hasCharSum_residual`), so the coefficient of the
`k`-th power of the residual is the `k`-fold convolution power: a sum
over the decompositions `ν = ν₁ + ⋯ + ν_k` into nonzero dual modes.
Applying the coefficient functional to the *finite* `K`-term
truncation — where linearity is elementary — and bounding the
remainder by the supremum norm of the uniform pointwise estimate
(`norm_mFourierCoeff_le`) gives the finite cluster approximation

    ‖ℓ_ν − clusterPartial K ν‖ ≤ W^(K+1)/(1 − W)

at every nonzero frequency
(`norm_logMassCoeff_sub_clusterPartial_le`). No interchange with the
infinite logarithm series is hidden inside it.

At second order this reads

    ℓ_ν = w_ν − ½ Σ_μ w_μ w_{ν−μ} + O(W³)

(`norm_logMassCoeff_sub_second_order_le`), the sum running over
nonzero modes only. Nothing here claims that any coefficient is
nonzero. -/

namespace Theaetetus

open UnitAddTorus MeasureTheory Complex

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## Orthogonality of the characters -/

/-- A character other than the trivial one integrates to zero: shift
the integral by a point where the character is not `1`. -/
theorem integral_mFourier (κ : Fin d → ℤ) :
    (∫ z : UnitAddTorus (Fin d), mFourier κ z
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
      = if κ = 0 then 1 else 0 := by
  by_cases hκ : κ = 0
  · subst hκ
    simp [mFourier]
  · rw [if_neg hκ]
    obtain ⟨i, hi⟩ : ∃ i, κ i ≠ 0 := by
      by_contra hall
      exact hκ (funext fun i => by
        simpa using not_not.mp (not_exists.mp hall i))
    set x : Fin d → ℝ :=
      fun j => if j = i then (1 : ℝ) / (2 * (κ i : ℝ)) else 0 with hx
    have hiR : ((κ i : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hi
    have hpair : dualPairing κ x = 1 / 2 := by
      rw [dualPairing, Finset.sum_eq_single i]
      · show ((κ i : ℤ) : ℝ)
            * (if i = i then (1 : ℝ) / (2 * (κ i : ℝ)) else 0) = 1 / 2
        rw [if_pos rfl]
        field_simp
      · intro j _ hj
        simp [hx, hj]
      · simp
    have hchar : mFourier κ (torusMk x) = -1 := by
      rw [mFourier_torusMk, hpair]
      rw [show (2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ))
          = (Real.pi : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_pi_mul_I
    have hshift : (∫ z : UnitAddTorus (Fin d),
          mFourier κ (torusMk x + z)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
        = ∫ z : UnitAddTorus (Fin d), mFourier κ z
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
      integral_add_left_eq_self _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
      mFourier_point_add κ (torusMk x) z), hchar,
      integral_const_mul] at hshift
    linear_combination (-1 / 2 : ℂ) * hshift

/-- Orthogonality under the coefficient functional. -/
theorem mFourierCoeff_mFourier (m ν : Fin d → ℤ) :
    mFourierCoeff (fun z => mFourier m z) ν = if m = ν then 1 else 0 := by
  have hprod : ∀ z : UnitAddTorus (Fin d),
      mFourier (-ν) z • mFourier m z = mFourier (m + -ν) z := by
    intro z
    rw [mFourier_add, smul_eq_mul, mul_comm]
  rw [show mFourierCoeff (fun z => mFourier m z) ν
      = ∫ z : UnitAddTorus (Fin d), mFourier (-ν) z • mFourier m z
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) from rfl,
    integral_congr_ae (Filter.Eventually.of_forall hprod), integral_mFourier]
  by_cases h : m = ν
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hz
    exact h (by rwa [add_neg_eq_zero] at hz)

theorem mFourier_zero_eq (z : UnitAddTorus (Fin d)) :
    mFourier (0 : Fin d → ℤ) z = 1 := by
  simp [mFourier]

theorem norm_mFourier (n : Fin d → ℤ) (z : UnitAddTorus (Fin d)) :
    ‖mFourier n z‖ = 1 := by
  show ‖∏ i, fourier (n i) (z i)‖ = 1
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => Circle.norm_coe _

/-! ## Absolutely convergent character series -/

/-- A function on the torus presented by an absolutely summable
character series. -/
structure HasCharSum (a : (Fin d → ℤ) → ℂ)
    (f : UnitAddTorus (Fin d) → ℂ) : Prop where
  summable : Summable a
  hasSum : ∀ z, HasSum (fun m => a m * mFourier m z) (f z)

/-- **Coefficient uniqueness**: the torus Fourier coefficient of an
absolutely convergent character series is the corresponding entry of
its coefficient sequence. The interchange is legitimate because the
characters are unimodular and the measure is a probability
measure. -/
theorem HasCharSum.mFourierCoeff_eq {a : (Fin d → ℤ) → ℂ}
    {f : UnitAddTorus (Fin d) → ℂ} (h : HasCharSum a f) (ν : Fin d → ℤ) :
    mFourierCoeff f ν = a ν := by
  set μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle with hμ
  set F : (Fin d → ℤ) → UnitAddTorus (Fin d) → ℂ :=
    fun m z => mFourier (-ν) z • (a m * mFourier m z) with hF
  have hmeas : ∀ m, AEStronglyMeasurable (F m) μ := fun m =>
    (((mFourier (-ν)).continuous.smul
      ((continuous_const).mul (mFourier m).continuous))).aestronglyMeasurable
  have hnorm : ∀ m z, ‖F m z‖ = ‖a m‖ := by
    intro m z
    rw [hF]
    simp only [smul_eq_mul, norm_mul, norm_mFourier, one_mul, mul_one]
  have hfin : ∑' m : Fin d → ℤ, ∫⁻ z, ‖F m z‖ₑ ∂μ ≠ ⊤ := by
    have hval : ∀ m : Fin d → ℤ, ∫⁻ z, ‖F m z‖ₑ ∂μ = (‖a m‖₊ : ENNReal) := by
      intro m
      rw [show (fun z => ‖F m z‖ₑ) = fun _ : UnitAddTorus (Fin d) =>
        ((‖a m‖₊ : ENNReal)) from funext fun z => by
          simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
          exact NNReal.coe_injective (hnorm m z)]
      simp [hμ]
    rw [tsum_congr hval, ENNReal.tsum_coe_ne_top_iff_summable]
    exact NNReal.summable_coe.mp
      (by simpa using summable_norm_iff.mpr h.summable)
  have hpt : ∀ z, mFourier (-ν) z • f z = ∑' m, F m z := by
    intro z
    rw [smul_eq_mul, ← (h.hasSum z).tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun m => rfl
  show ∫ z, mFourier (-ν) z • f z ∂μ = a ν
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_tsum hmeas hfin]
  have hterm : ∀ m : Fin d → ℤ, (∫ z, F m z ∂μ)
      = if m = ν then a ν else 0 := by
    intro m
    rw [show (∫ z, F m z ∂μ) = a m * mFourierCoeff (fun z => mFourier m z) ν
      from by
        rw [show mFourierCoeff (fun z => mFourier m z) ν
          = ∫ z, mFourier (-ν) z • mFourier m z ∂μ from rfl,
          ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
          rw [hF]
          simp only [smul_eq_mul]
          ring),
      mFourierCoeff_mFourier]
    by_cases hm : m = ν
    · subst hm
      simp
    · simp [hm]
  rw [tsum_congr hterm, tsum_ite_eq]

/-! ## Convolution -/

/-- Discrete convolution on the dual lattice. -/
noncomputable def convolve (a b : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  fun ν => ∑' μ : Fin d → ℤ, a μ * b (ν - μ)

/-- Regrouping a product family by the sum of its indices. -/
private def shiftEquiv (d : ℕ) :
    ((Fin d → ℤ) × (Fin d → ℤ)) ≃ ((Fin d → ℤ) × (Fin d → ℤ)) where
  toFun q := (q.2, q.1 - q.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv q := by
    ext j <;> simp
  right_inv p := by
    ext j <;> simp

/-- **Regrouping**: an absolutely summable product family, summed
along the fibers of the index sum, gives the convolution. -/
private theorem hasSum_convolve_of_hasSum {F : (Fin d → ℤ) × (Fin d → ℤ) → ℂ}
    {S : ℂ} (hF : HasSum F S) (hnorm : Summable fun p => ‖F p‖) :
    HasSum (fun ν : Fin d → ℤ => ∑' μ : Fin d → ℤ, F (μ, ν - μ)) S := by
  have hcomp : HasSum (F ∘ (shiftEquiv d)) S :=
    (shiftEquiv d).hasSum_iff.mpr hF
  refine hcomp.prod_fiberwise fun ν => ?_
  have hsum : Summable fun μ : Fin d → ℤ => F (μ, ν - μ) := by
    refine (hnorm.comp_injective ?_).of_norm
    intro p q hpq
    simpa using hpq
  exact hsum.hasSum.congr_fun fun μ => rfl

/-- **The product theorem**: the coefficient sequence of a product of
absolutely convergent character series is the convolution of their
coefficient sequences. -/
theorem HasCharSum.mul {a b : (Fin d → ℤ) → ℂ}
    {f g : UnitAddTorus (Fin d) → ℂ} (ha : HasCharSum a f)
    (hb : HasCharSum b g) :
    HasCharSum (convolve a b) (fun z => f z * g z) := by
  have hna : Summable fun m => ‖a m‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun m => ‖b m‖ := summable_norm_iff.mpr hb.summable
  have hmul : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
      ‖a p.1‖ * ‖b p.2‖ :=
    hna.mul_of_nonneg hnb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  constructor
  · have hnormp : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
        ‖a p.1 * b p.2‖ := by
      simpa only [norm_mul] using hmul
    exact (hasSum_convolve_of_hasSum hnormp.of_norm.hasSum hnormp).summable
  · intro z
    set A : (Fin d → ℤ) → ℂ := fun m => a m * mFourier m z with hA
    set B : (Fin d → ℤ) → ℂ := fun m => b m * mFourier m z with hB
    have hnA : ∀ m, ‖A m‖ = ‖a m‖ := fun m => by
      rw [hA]
      simp only [norm_mul, norm_mFourier, mul_one]
    have hnB : ∀ m, ‖B m‖ = ‖b m‖ := fun m => by
      rw [hB]
      simp only [norm_mul, norm_mFourier, mul_one]
    have h1 : HasSum A (f z) := ha.hasSum z
    have h2 : HasSum B (g z) := hb.hasSum z
    have hnormF : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
        ‖A p.1 * B p.2‖ := by
      refine hmul.congr fun p => ?_
      rw [norm_mul, hnA, hnB]
    have hFsum : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
        A p.1 * B p.2 :=
      summable_mul_of_summable_norm
        (hna.congr fun m => (hnA m).symm) (hnb.congr fun m => (hnB m).symm)
    have hF : HasSum (fun p : (Fin d → ℤ) × (Fin d → ℤ) => A p.1 * B p.2)
        (f z * g z) := h1.mul h2 hFsum
    have hconv := hasSum_convolve_of_hasSum hF hnormF
    refine hconv.congr_fun fun ν => ?_
    have hchar : ∀ μ : Fin d → ℤ,
        A μ * B (ν - μ) = (a μ * b (ν - μ)) * mFourier ν z := by
      intro μ
      have hadd : mFourier μ z * mFourier (ν - μ) z = mFourier ν z := by
        rw [← mFourier_add]
        congr 1
        ext j
        simp
      rw [hA, hB]
      calc (a μ * mFourier μ z) * (b (ν - μ) * mFourier (ν - μ) z)
          = (a μ * b (ν - μ)) * (mFourier μ z * mFourier (ν - μ) z) := by
            ring
        _ = (a μ * b (ν - μ)) * mFourier ν z := by rw [hadd]
    rw [tsum_congr hchar, tsum_mul_right]
    rfl

/-- The `k`-fold convolution power, indexed so that `convPow a k` is
the coefficient sequence of the `(k+1)`-st power. -/
noncomputable def convPow (a : (Fin d → ℤ) → ℂ) : ℕ → (Fin d → ℤ) → ℂ
  | 0 => a
  | k + 1 => convolve a (convPow a k)

theorem HasCharSum.pow {a : (Fin d → ℤ) → ℂ}
    {f : UnitAddTorus (Fin d) → ℂ} (ha : HasCharSum a f) :
    ∀ k : ℕ, HasCharSum (convPow a k) (fun z => f z ^ (k + 1))
  | 0 => by
      refine ⟨ha.summable, fun z => ?_⟩
      simpa [convPow] using ha.hasSum z
  | k + 1 => by
      have hk := ha.mul (HasCharSum.pow ha k)
      refine ⟨hk.summable, fun z => ?_⟩
      have := hk.hasSum z
      rwa [show f z * f z ^ (k + 1) = f z ^ (k + 1 + 1) by ring] at this

/-! ## The residual as a character series -/

/-- The residual on the torus. -/
noncomputable def residualTorus (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) :
    UnitAddTorus (Fin d) → ℝ :=
  fun z => torusPeriodization ((α / Real.pi) • M) z / zeroMode M α - 1

theorem residualTorus_mk (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (x : Fin d → ℝ) : residualTorus M α (torusMk x) = residual M α x := by
  show torusPeriodization ((α / Real.pi) • M) (torusMk x) / zeroMode M α - 1
    = gramMass M α x / zeroMode M α - 1
  rw [torusPeriodization_mk, ← gramMass_eq_periodization]

/-- The complex coefficient sequence of the residual: the relative
mode weights, with the zero mode deleted. -/
noncomputable def modeCoeff (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (m : Fin d → ℤ) : ℂ :=
  if m = 0 then 0 else ((modeWeight M α m : ℝ) : ℂ)

theorem summable_modeCoeff (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    Summable (modeCoeff M α) := by
  refine Summable.of_norm ?_
  refine ((hasSum_totalWeight hM hα).summable).congr fun m => ?_
  by_cases hm : m = 0
  · simp [modeCoeff, hm]
  · simp only [modeCoeff, hm, if_false, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (modeWeight_pos hM hα m)]

/-- **The residual is an absolutely convergent character series** with
no zero mode. -/
theorem hasCharSum_residual (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    HasCharSum (modeCoeff M α)
      (fun z => ((residualTorus M α z : ℝ) : ℂ)) := by
  refine ⟨summable_modeCoeff hM hα, fun z => ?_⟩
  obtain ⟨x, rfl⟩ := torusMk_surjective z
  have h0 : ((zeroMode M α : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (zeroMode_pos hM hα).ne'
  have hfull := (hasSum_massFourier hM hα x).div_const
    ((zeroMode M α : ℝ) : ℂ)
  have hone := hasSum_ite_eq (0 : Fin d → ℤ) (1 : ℂ)
  have hsub := hfull.sub hone
  have hval : ((gramMass M α x : ℝ) : ℂ) / ((zeroMode M α : ℝ) : ℂ) - 1
      = ((residualTorus M α (torusMk x) : ℝ) : ℂ) := by
    rw [residualTorus_mk, residual]
    push_cast
    ring
  rw [hval] at hsub
  refine hsub.congr_fun fun m => ?_
  by_cases hm : m = 0
  · subst hm
    rw [modeCoeff, if_pos rfl, if_pos rfl, zero_mul]
    rw [show ((massFourierCoeff M α 0 : ℝ) : ℂ) = ((zeroMode M α : ℝ) : ℂ)
      from rfl, mFourier_zero_eq, mul_one, div_self h0, sub_self]
  · rw [modeCoeff, if_neg hm, if_neg hm, sub_zero, modeWeight]
    push_cast
    ring

/-! ## Linearity and the sup bound of the coefficient functional -/

private theorem integrableT {f : UnitAddTorus (Fin d) → ℂ}
    (hf : Continuous f) :
    Integrable f (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem coeff_integral (f : UnitAddTorus (Fin d) → ℂ)
    (ν : Fin d → ℤ) :
    mFourierCoeff f ν
      = ∫ z : UnitAddTorus (Fin d), mFourier (-ν) z • f z
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := rfl

private theorem mFourierCoeff_sub {f g : UnitAddTorus (Fin d) → ℂ}
    (hf : Continuous f) (hg : Continuous g) (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => f z - g z) ν
      = mFourierCoeff f ν - mFourierCoeff g ν := by
  have hif : Integrable (fun z => mFourier (-ν) z • f z)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
    integrableT ((mFourier (-ν)).continuous.smul hf)
  have hig : Integrable (fun z => mFourier (-ν) z • g z)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
    integrableT ((mFourier (-ν)).continuous.smul hg)
  rw [coeff_integral, coeff_integral, coeff_integral,
    ← integral_sub hif hig]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
    smul_sub (mFourier (-ν) z) (f z) (g z))

private theorem mFourierCoeff_const_mul (c : ℂ)
    (f : UnitAddTorus (Fin d) → ℂ) (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => c * f z) ν = c * mFourierCoeff f ν := by
  rw [coeff_integral, coeff_integral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  ring

private theorem mFourierCoeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → UnitAddTorus (Fin d) → ℂ) (hF : ∀ i, Continuous (F i))
    (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => ∑ i ∈ s, F i z) ν
      = ∑ i ∈ s, mFourierCoeff (F i) ν := by
  have hint : ∀ i, Integrable (fun z => mFourier (-ν) z • F i z)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := fun i =>
    integrableT ((mFourier (-ν)).continuous.smul (hF i))
  rw [coeff_integral,
    show (fun z => mFourier (-ν) z • ∑ i ∈ s, F i z)
      = fun z => ∑ i ∈ s, mFourier (-ν) z • F i z from funext fun z =>
      Finset.smul_sum,
    integral_finsetSum s fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => (coeff_integral (F i) ν).symm

private theorem mFourierCoeff_const (c : ℂ) {ν : Fin d → ℤ} (hν : ν ≠ 0) :
    mFourierCoeff (fun _ : UnitAddTorus (Fin d) => c) ν = 0 := by
  rw [show (fun _ : UnitAddTorus (Fin d) => c)
      = fun z => c * mFourier (0 : Fin d → ℤ) z from funext fun z => by
    rw [mFourier_zero_eq, mul_one],
    mFourierCoeff_const_mul, mFourierCoeff_mFourier, if_neg (Ne.symm hν),
    mul_zero]

/-- The coefficient functional is bounded by the supremum norm: the
characters are unimodular and the measure is a probability measure. -/
theorem norm_mFourierCoeff_le {f : UnitAddTorus (Fin d) → ℂ} {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (ν : Fin d → ℤ) : ‖mFourierCoeff f ν‖ ≤ C := by
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (f := fun z => mFourier (-ν) z • f z) (C := C)
    (Filter.Eventually.of_forall fun z => by
      rw [smul_eq_mul, norm_mul, norm_mFourier, one_mul]
      exact hC z)
  rw [coeff_integral]
  refine le_trans hbound (le_of_eq ?_)
  simp

/-! ## The finite cluster approximation -/

theorem continuous_residualTorus (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    Continuous (residualTorus M α) :=
  ((continuous_torusPeriodization
    (posDef_smul' hM (div_pos hα Real.pi_pos))).div_const _).sub
    continuous_const

/-- The `K`-term cluster approximation to the coefficient at `ν`: a
sum over the decompositions of `ν` into at most `K` dual modes. -/
noncomputable def clusterPartial (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (K : ℕ) (ν : Fin d → ℤ) : ℂ :=
  ∑ k ∈ Finset.range K,
    ((-1 : ℂ) ^ k / (k + 1)) * convPow (modeCoeff M α) k ν

private theorem norm_logMassTorus_sub_partial (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) (K : ℕ)
    (z : UnitAddTorus (Fin d)) :
    ‖((logMassTorus M α z : ℝ) : ℂ)
        - ((Real.log (zeroMode M α) : ℝ) : ℂ)
        - ∑ k ∈ Finset.range K,
            ((-1 : ℂ) ^ k / (k + 1))
              * ((residualTorus M α z : ℝ) : ℂ) ^ (k + 1)‖
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) := by
  obtain ⟨x, rfl⟩ := torusMk_surjective z
  have hreal := abs_logMass_sub_partialSum_le hM hα hw K x
  rw [logMassTorus_mk, residualTorus_mk]
  rw [show ((logMass M α x : ℝ) : ℂ) - ((Real.log (zeroMode M α) : ℝ) : ℂ)
        - ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k / (k + 1))
            * ((residual M α x : ℝ) : ℂ) ^ (k + 1)
      = ((logMass M α x - Real.log (zeroMode M α)
          - ∑ k ∈ Finset.range K,
              (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1) : ℝ) : ℂ) by
    push_cast
    refine congrArg (fun t : ℂ => ((logMass M α x : ℝ) : ℂ)
      - ((Real.log (zeroMode M α) : ℝ) : ℂ) - t) ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hreal

/-- **The finite cluster approximation**: at a nonzero frequency the
coefficient of the logarithmic mass is its `K`-term cluster sum, up
to an error controlled by the total weight alone. No infinite-series
interchange is hidden here: the coefficient functional is applied to
a finite sum, and the error comes from the uniform pointwise
remainder. -/
theorem norm_logMassCoeff_sub_clusterPartial_le (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) (K : ℕ) {ν : Fin d → ℤ}
    (hν : ν ≠ 0) :
    ‖logMassCoeff M α ν - clusterPartial M α K ν‖
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) := by
  have hRc : Continuous fun z : UnitAddTorus (Fin d) =>
      ((residualTorus M α z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_residualTorus hM hα)
  have hLc : Continuous fun z : UnitAddTorus (Fin d) =>
      ((logMassTorus M α z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_logMassTorus hM hα)
  have hFk : ∀ k : ℕ, Continuous fun z : UnitAddTorus (Fin d) =>
      ((-1 : ℂ) ^ k / (k + 1)) * ((residualTorus M α z : ℝ) : ℂ) ^ (k + 1) :=
    fun k => continuous_const.mul (hRc.pow _)
  have hP : Continuous fun z : UnitAddTorus (Fin d) =>
      ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k / (k + 1))
        * ((residualTorus M α z : ℝ) : ℂ) ^ (k + 1) :=
    continuous_finsetSum _ fun k _ => hFk k
  have hcoeffP : mFourierCoeff (fun z : UnitAddTorus (Fin d) =>
      ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k / (k + 1))
        * ((residualTorus M α z : ℝ) : ℂ) ^ (k + 1)) ν
      = clusterPartial M α K ν := by
    rw [mFourierCoeff_finset_sum _ _ hFk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mFourierCoeff_const_mul,
      ((hasCharSum_residual hM hα).pow k).mFourierCoeff_eq ν]
  have hcoeffL : mFourierCoeff (fun z : UnitAddTorus (Fin d) =>
      ((logMassTorus M α z : ℝ) : ℂ)
        - ((Real.log (zeroMode M α) : ℝ) : ℂ)) ν = logMassCoeff M α ν := by
    rw [mFourierCoeff_sub hLc continuous_const,
      mFourierCoeff_const _ hν, sub_zero]
    rfl
  have hsplit := mFourierCoeff_sub
    (f := fun z : UnitAddTorus (Fin d) => ((logMassTorus M α z : ℝ) : ℂ)
      - ((Real.log (zeroMode M α) : ℝ) : ℂ))
    (g := fun z : UnitAddTorus (Fin d) =>
      ∑ k ∈ Finset.range K, ((-1 : ℂ) ^ k / (k + 1))
        * ((residualTorus M α z : ℝ) : ℂ) ^ (k + 1))
    (hLc.sub continuous_const) hP ν
  rw [hcoeffL, hcoeffP] at hsplit
  rw [← hsplit]
  refine norm_mFourierCoeff_le (fun z => ?_) ν
  exact norm_logMassTorus_sub_partial hM hα hw K z

/-- **The second-order cluster form**: the coefficient is the direct
mode less half the two-mode convolution, with an error cubic in the
total weight. The zero mode is excluded throughout by
`modeCoeff`. -/
theorem norm_logMassCoeff_sub_second_order_le (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) {ν : Fin d → ℤ} (hν : ν ≠ 0) :
    ‖logMassCoeff M α ν
        - (modeCoeff M α ν
          - (1 / 2) * convolve (modeCoeff M α) (modeCoeff M α) ν)‖
      ≤ totalWeight M α ^ 3 / (1 - totalWeight M α) := by
  have h := norm_logMassCoeff_sub_clusterPartial_le hM hα hw 2 hν
  have hval : clusterPartial M α 2 ν
      = modeCoeff M α ν
        - (1 / 2) * convolve (modeCoeff M α) (modeCoeff M α) ν := by
    rw [clusterPartial, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    show 0 + ((-1 : ℂ) ^ 0 / ((0 : ℕ) + 1)) * convPow (modeCoeff M α) 0 ν
        + ((-1 : ℂ) ^ 1 / ((1 : ℕ) + 1)) * convPow (modeCoeff M α) 1 ν = _
    show 0 + ((-1 : ℂ) ^ 0 / ((0 : ℕ) + 1)) * modeCoeff M α ν
        + ((-1 : ℂ) ^ 1 / ((1 : ℕ) + 1))
          * convolve (modeCoeff M α) (modeCoeff M α) ν = _
    push_cast
    ring
  rwa [hval] at h

end Theaetetus
