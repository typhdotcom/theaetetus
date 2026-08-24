import Theaetetus.EvenPartSeparation

/-! # The torus Fourier coefficients of the logarithmic mass

The logarithmic mass is `ℤᵈ`-periodic, so it descends to the unit
torus (`logMassTorus`), where the Gaussian periodization already
lives. Positivity of the mass makes the logarithm well defined and
continuous (`continuous_logMassTorus`), so the torus Fourier
coefficients of Mathlib's multivariate transform are available
(`logMassCoeff`). The mass is real and even, so the coefficients are
real and symmetric under frequency negation (`logMassCoeff_conj`,
`logMassCoeff_neg`, `logMassCoeff_eq_ofReal`).

The equation the rigidity route needs falls out by applying the
coefficient functional to two functions that are literally equal, no
reconstruction of the field from its series involved. If the even
part of the logarithmic mass about `a` agrees with the even part
about `b`, then at every dual frequency

    ℓ_ν · cos(2π⟨ν, a⟩) = ℓ_ν · cos(2π⟨ν, b⟩)

(`logMassCoeff_cos_eq`), because the coefficient of `w ↦ L(a + w)` is
`ℓ_ν` times the character at `a`, and the coefficient of
`w ↦ L(a − w)` is `ℓ_ν` times its conjugate.

Where a coefficient is nonzero this reads `⟨ν, a − b⟩ ∈ ℤ` or
`⟨ν, a + b⟩ ∈ ℤ`. The singleton frequencies `freqSingle i` put each
coordinate on one of those two branches; the pair frequencies
`freqPair i j` forbid a coordinate forced onto one branch from
coexisting with a coordinate forced onto the other. That is exactly
the arithmetic already isolated in `isLatticeShift_or_of_pairwise`,
so nonvanishing on that finite family — and on nothing else —
implies the even-part property (`FiniteCertificate`,
`evenPartSeparating_of_finiteCertificate`) and with it the whole
coprime rigidity statement
(`gramDefect_neg_of_finiteCertificate`). Composed with the block
obstruction, the certificate is also formally a diagnostic for
orthogonal splitting: a form whose coordinates split with no cross
terms admits no finite certificate
(`not_finiteCertificate_of_split`).

Nonvanishing itself is not proved, assumed, or estimated here. -/

namespace Theaetetus

open UnitAddTorus MeasureTheory Complex

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## The characters, as functions of the point -/

theorem mFourier_point_add (n : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp [mFourier, fourier_apply, smul_add, AddCircle.toCircle_add,
    Finset.prod_mul_distrib]

theorem mFourier_point_neg (n : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    mFourier n (-x) = mFourier (-n) x := by
  simp [mFourier, fourier_apply]

theorem mFourier_mul_neg (n : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    mFourier n x * mFourier (-n) x = 1 := by
  rw [← mFourier_add]
  simp [mFourier]

/-! ## The descent -/

/-- The logarithmic mass on the unit torus, through the Gaussian
periodization of the rescaled form. -/
noncomputable def logMassTorus (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) :
    UnitAddTorus (Fin d) → ℝ :=
  fun z => Real.log (torusPeriodization ((α / Real.pi) • M) z)

theorem logMassTorus_mk (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (x : Fin d → ℝ) : logMassTorus M α (torusMk x) = logMass M α x := by
  show Real.log (torusPeriodization ((α / Real.pi) • M) (torusMk x))
    = Real.log (gramMass M α x)
  rw [torusPeriodization_mk, ← gramMass_eq_periodization]

theorem torusPeriodization_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (z : UnitAddTorus (Fin d)) :
    0 < torusPeriodization ((α / Real.pi) • M) z := by
  obtain ⟨x, rfl⟩ := torusMk_surjective z
  rw [torusPeriodization_mk, ← gramMass_eq_periodization]
  exact gramMass_pos hM hα x

theorem continuous_logMassTorus (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    Continuous (logMassTorus M α) := by
  exact (continuous_torusPeriodization
    (posDef_smul' hM (div_pos hα Real.pi_pos))).log
    fun z => (torusPeriodization_pos hM hα z).ne'

theorem logMassTorus_neg (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (z : UnitAddTorus (Fin d)) :
    logMassTorus M α (-z) = logMassTorus M α z := by
  obtain ⟨x, rfl⟩ := torusMk_surjective z
  have hneg : -torusMk x = torusMk (-x) := by
    funext i
    show -(x i : UnitAddCircle) = ((-x i : ℝ) : UnitAddCircle)
    simp
  rw [hneg, logMassTorus_mk, logMassTorus_mk]
  show Real.log (gramMass M α (-x)) = Real.log (gramMass M α x)
  rw [gramMass_neg]

/-! ## The coefficients, their symmetry, and the functional -/

/-- The Haar probability measure on the unit torus, in the form the
Fourier coefficient is defined against. -/
private noncomputable abbrev torusHaar (d : ℕ) :
    Measure (UnitAddTorus (Fin d)) :=
  Measure.pi fun _ : Fin d => AddCircle.haarAddCircle

private theorem mFourierCoeff_integral (f : UnitAddTorus (Fin d) → ℂ)
    (ν : Fin d → ℤ) :
    mFourierCoeff f ν
      = ∫ z : UnitAddTorus (Fin d), mFourier (-ν) z • f z ∂torusHaar d :=
  rfl

private theorem measurePreserving_torusNeg :
    MeasurePreserving (fun z : UnitAddTorus (Fin d) => -z)
      (torusHaar d) (torusHaar d) :=
  @measurePreserving_pi (Fin d) _ _ _ _ _
    (fun _ => AddCircle.haarAddCircle) (fun _ => AddCircle.haarAddCircle)
    (fun _ z => -z) (fun _ => inferInstance)
    (fun _ => Measure.measurePreserving_neg _)

private theorem integral_torus_neg (f : UnitAddTorus (Fin d) → ℂ) :
    (∫ z : UnitAddTorus (Fin d), f (-z) ∂torusHaar d)
      = ∫ z : UnitAddTorus (Fin d), f z ∂torusHaar d :=
  measurePreserving_torusNeg.integral_comp
    (MeasurableEquiv.neg (UnitAddTorus (Fin d))).measurableEmbedding f

private theorem integral_torus_add (f : UnitAddTorus (Fin d) → ℂ)
    (a : UnitAddTorus (Fin d)) :
    (∫ z : UnitAddTorus (Fin d), f (a + z) ∂torusHaar d)
      = ∫ z : UnitAddTorus (Fin d), f z ∂torusHaar d :=
  integral_add_left_eq_self f a

private theorem integrable_torus {f : UnitAddTorus (Fin d) → ℂ}
    (hf : Continuous f) : Integrable f (torusHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Reflecting the point inverts the frequency. -/
theorem mFourierCoeff_comp_neg (f : UnitAddTorus (Fin d) → ℂ)
    (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => f (-z)) ν = mFourierCoeff f (-ν) := by
  rw [mFourierCoeff_integral, mFourierCoeff_integral,
    ← integral_torus_neg (fun z => mFourier (- -ν) z • f z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show mFourier (-ν) z • f (-z) = mFourier (- -ν) (-z) • f (-z)
  rw [mFourier_point_neg, neg_neg]

/-- Translating the point multiplies by the character. -/
theorem mFourierCoeff_comp_add (f : UnitAddTorus (Fin d) → ℂ)
    (a : UnitAddTorus (Fin d)) (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => f (a + z)) ν
      = mFourier ν a * mFourierCoeff f ν := by
  rw [mFourierCoeff_integral, mFourierCoeff_integral,
    ← integral_torus_add (fun z => mFourier (-ν) z • f z) a,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show mFourier (-ν) z • f (a + z)
    = mFourier ν a * (mFourier (-ν) (a + z) • f (a + z))
  rw [mFourier_point_add, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    mFourier_mul_neg, one_mul]

/-- The coefficient functional is additive on continuous functions. -/
theorem mFourierCoeff_add_of_continuous {f g : UnitAddTorus (Fin d) → ℂ}
    (hf : Continuous f) (hg : Continuous g) (ν : Fin d → ℤ) :
    mFourierCoeff (fun z => f z + g z) ν
      = mFourierCoeff f ν + mFourierCoeff g ν := by
  rw [mFourierCoeff_integral, mFourierCoeff_integral, mFourierCoeff_integral,
    integral_congr_ae (Filter.Eventually.of_forall fun z =>
      smul_add (mFourier (-ν) z) (f z) (g z))]
  exact integral_add (integrable_torus ((mFourier (-ν)).continuous.smul hf))
    (integrable_torus ((mFourier (-ν)).continuous.smul hg))

/-- The torus Fourier coefficient of the logarithmic mass. -/
noncomputable def logMassCoeff (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) : ℂ :=
  mFourierCoeff (fun z => ((logMassTorus M α z : ℝ) : ℂ)) ν

theorem mFourier_conj (n : Fin d → ℤ) (z : UnitAddTorus (Fin d)) :
    (starRingEnd ℂ) (mFourier n z) = mFourier (-n) z := by
  show (starRingEnd ℂ) (∏ i, fourier (n i) (z i))
    = ∏ i, fourier ((-n) i) (z i)
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => (fourier_neg).symm

/-- The mass is even, so negating the frequency preserves the
coefficient. -/
theorem logMassCoeff_neg (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) : logMassCoeff M α (-ν) = logMassCoeff M α ν := by
  have h := mFourierCoeff_comp_neg
    (fun z : UnitAddTorus (Fin d) => ((logMassTorus M α z : ℝ) : ℂ)) ν
  have hfun : (fun z : UnitAddTorus (Fin d) =>
      ((logMassTorus M α (-z) : ℝ) : ℂ))
      = fun z : UnitAddTorus (Fin d) => ((logMassTorus M α z : ℝ) : ℂ) := by
    funext z
    rw [logMassTorus_neg]
  rw [hfun] at h
  exact h.symm

/-- The mass is real, so conjugation inverts the frequency. -/
theorem logMassCoeff_conj (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) :
    (starRingEnd ℂ) (logMassCoeff M α ν) = logMassCoeff M α (-ν) := by
  rw [logMassCoeff, logMassCoeff, mFourierCoeff_integral,
    mFourierCoeff_integral, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (starRingEnd ℂ) (mFourier (-ν) z • ((logMassTorus M α z : ℝ) : ℂ))
    = mFourier (- -ν) z • ((logMassTorus M α z : ℝ) : ℂ)
  rw [smul_eq_mul, smul_eq_mul, map_mul, mFourier_conj, Complex.conj_ofReal]

/-- Every coefficient is real: the mass is both real and even. -/
theorem logMassCoeff_im (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) : (logMassCoeff M α ν).im = 0 := by
  have h : (starRingEnd ℂ) (logMassCoeff M α ν) = logMassCoeff M α ν := by
    rw [logMassCoeff_conj, logMassCoeff_neg]
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

/-- The real coefficient. -/
noncomputable def logMassRe (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) : ℝ := (logMassCoeff M α ν).re

theorem logMassCoeff_eq_ofReal (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) :
    logMassCoeff M α ν = ((logMassRe M α ν : ℝ) : ℂ) := by
  refine Complex.ext rfl ?_
  rw [Complex.ofReal_im, logMassCoeff_im]

theorem logMassRe_neg (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (ν : Fin d → ℤ) : logMassRe M α (-ν) = logMassRe M α ν := by
  show (logMassCoeff M α (-ν)).re = (logMassCoeff M α ν).re
  rw [logMassCoeff_neg]

/-! ## The coefficient equation from equality of even parts -/

theorem dualPairing_freq_add (m n : Fin d → ℤ) (x : Fin d → ℝ) :
    dualPairing (m + n) x = dualPairing m x + dualPairing n x := by
  simp only [dualPairing, Pi.add_apply, Int.cast_add, add_mul]
  exact Finset.sum_add_distrib

theorem dualPairing_freq_neg (m : Fin d → ℤ) (x : Fin d → ℝ) :
    dualPairing (-m) x = -dualPairing m x := by
  simp [dualPairing, neg_mul, Finset.sum_neg_distrib]

private theorem torusMk_add (x y : Fin d → ℝ) :
    torusMk (x + y) = torusMk x + torusMk y := by
  funext i
  show ((x i + y i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) + (y i)
  rfl

private theorem torusMk_sub (x y : Fin d → ℝ) :
    torusMk (x - y) = -torusMk y + torusMk x := by
  funext i
  show ((x i - y i : ℝ) : UnitAddCircle)
    = -(y i : UnitAddCircle) + (x i : UnitAddCircle)
  rw [show x i - y i = -y i + x i by ring]
  rfl

/-- The two characters at a lifted point sum to twice a cosine. -/
theorem mFourier_add_neg_torusMk (ν : Fin d → ℤ) (c : Fin d → ℝ) :
    mFourier ν (torusMk c) + mFourier (-ν) (torusMk c)
      = ((2 * Real.cos (2 * Real.pi * dualPairing ν c) : ℝ) : ℂ) := by
  rw [mFourier_torusMk, mFourier_torusMk, dualPairing_freq_neg]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * ((dualPairing ν c : ℝ) : ℂ))
      = ((2 * Real.pi * dualPairing ν c : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((-dualPairing ν c : ℝ) : ℂ))
      = -((2 * Real.pi * dualPairing ν c : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, ← Complex.two_cos, ← Complex.ofReal_cos]
  push_cast
  ring

/-- **The coefficient equation**: if the even part of the logarithmic
mass about `a` agrees with the even part about `b`, then every dual
frequency sees the same cosine, weighted by its coefficient. The
coefficient functional is applied to two functions that are equal;
the field is never reconstructed from its series. -/
theorem logMassCoeff_cos_eq (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    {a b : Fin d → ℝ}
    (h : ∀ v : Fin d → ℝ, logMass M α (a + v) + logMass M α (a - v)
      = logMass M α (b + v) + logMass M α (b - v)) (ν : Fin d → ℤ) :
    logMassRe M α ν * (2 * Real.cos (2 * Real.pi * dualPairing ν a))
      = logMassRe M α ν * (2 * Real.cos (2 * Real.pi * dualPairing ν b)) := by
  set G : UnitAddTorus (Fin d) → ℂ :=
    fun z => ((logMassTorus M α z : ℝ) : ℂ) with hG
  have hGc : Continuous G :=
    Complex.continuous_ofReal.comp (continuous_logMassTorus hM hα)
  have hval : ∀ c v : Fin d → ℝ,
      G (torusMk c + torusMk v) + G (-torusMk c + torusMk v)
        = ((logMass M α (c + v) : ℝ) : ℂ)
          + ((logMass M α (c - v) : ℝ) : ℂ) := by
    intro c v
    rw [← torusMk_add, ← torusMk_sub]
    simp only [hG, logMassTorus_mk]
    congr 2
    show Real.log (gramMass M α (v - c)) = Real.log (gramMass M α (c - v))
    rw [show v - c = -(c - v) by ring, gramMass_neg]
  have hfun : (fun w => G (torusMk a + w) + G (-torusMk a + w))
      = fun w => G (torusMk b + w) + G (-torusMk b + w) := by
    funext w
    obtain ⟨v, rfl⟩ := torusMk_surjective w
    rw [hval a v, hval b v]
    exact_mod_cast congrArg (fun t : ℝ => ((t : ℝ) : ℂ)) (h v)
  have hcoeff : ∀ c : Fin d → ℝ,
      mFourierCoeff (fun w => G (torusMk c + w) + G (-torusMk c + w)) ν
        = ((2 * Real.cos (2 * Real.pi * dualPairing ν c) : ℝ) : ℂ)
          * logMassCoeff M α ν := by
    intro c
    rw [mFourierCoeff_add_of_continuous
        (f := fun w => G (torusMk c + w)) (g := fun w => G (-torusMk c + w))
        (hGc.comp (continuous_const_add _))
        (hGc.comp (continuous_const_add _)),
      mFourierCoeff_comp_add, mFourierCoeff_comp_add]
    have hneg : mFourier ν (-torusMk c) = mFourier (-ν) (torusMk c) :=
      mFourier_point_neg ν (torusMk c)
    rw [hneg, ← add_mul, mFourier_add_neg_torusMk, hG]
    rfl
  have := hcoeff a
  rw [hfun, hcoeff b] at this
  rw [logMassCoeff_eq_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    at this
  have hr := Complex.ofReal_inj.mp this
  linear_combination -hr

/-! ## The finite frequency family -/

/-- The dual basis frequency at one coordinate. -/
def freqSingle (i : Fin d) : Fin d → ℤ := fun j => if j = i then 1 else 0

/-- The frequency mixing two coordinates. -/
def freqPair (i j : Fin d) : Fin d → ℤ := freqSingle i + freqSingle j

theorem dualPairing_freqSingle (i : Fin d) (x : Fin d → ℝ) :
    dualPairing (freqSingle i) x = x i := by
  rw [dualPairing, Finset.sum_eq_single i] <;>
    simp +contextual [freqSingle]

theorem dualPairing_freqPair (i j : Fin d) (x : Fin d → ℝ) :
    dualPairing (freqPair i j) x = x i + x j := by
  rw [freqPair, dualPairing_freq_add, dualPairing_freqSingle,
    dualPairing_freqSingle]

/-- **The finite certificate**: the coefficients do not vanish at the
singleton frequencies, nor at the frequencies mixing two distinct
coordinates. Nothing is asserted at any other frequency. -/
def FiniteCertificate (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : Prop :=
  (∀ i : Fin d, logMassRe M α (freqSingle i) ≠ 0)
    ∧ ∀ i j : Fin d, i ≠ j → logMassRe M α (freqPair i j) ≠ 0

/-! ## The conditional theorem -/

private theorem int_branch {s t : ℝ}
    (h : Real.cos (2 * Real.pi * s) = Real.cos (2 * Real.pi * t)) :
    (∃ k : ℤ, s - t = (k : ℝ)) ∨ ∃ k : ℤ, s + t = (k : ℝ) := by
  have hzero : Real.sin (Real.pi * (s + t)) * Real.sin (Real.pi * (s - t))
      = 0 := by
    have hd := Real.cos_sub_cos (2 * Real.pi * s) (2 * Real.pi * t)
    rw [h, sub_self] at hd
    have h1 : (2 * Real.pi * s + 2 * Real.pi * t) / 2
        = Real.pi * (s + t) := by ring
    have h2 : (2 * Real.pi * s - 2 * Real.pi * t) / 2
        = Real.pi * (s - t) := by ring
    rw [h1, h2] at hd
    linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rcases mul_eq_zero.mp hzero with hs | hs
  · right
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    exact ⟨n, mul_left_cancel₀ hpi (by linarith)⟩
  · left
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    exact ⟨n, mul_left_cancel₀ hpi (by linarith)⟩

/-- **The conditional theorem**: nonvanishing on the singleton and
distinct-pair frequencies implies that the even part of the
logarithmic mass determines its centre up to sign. Each nonzero
coefficient turns the coefficient equation into a choice of integral
branch, and the arithmetic of `isLatticeShift_or_of_pairwise` makes
one branch serve the whole vector. -/
theorem evenPartSeparating_of_finiteCertificate (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hc : FiniteCertificate M α) : EvenPartSeparating M α := by
  intro a b h
  have branch : ∀ ν : Fin d → ℤ, logMassRe M α ν ≠ 0 →
      (∃ k : ℤ, dualPairing ν a - dualPairing ν b = (k : ℝ))
        ∨ ∃ k : ℤ,
          dualPairing ν a + dualPairing ν b = (k : ℝ) := by
    intro ν hν
    refine int_branch ?_
    have hcos := mul_left_cancel₀ hν (logMassCoeff_cos_eq hM hα h ν)
    linarith
  refine isLatticeShift_or_of_pairwise ?_ ?_
  · intro i
    have hb := branch (freqSingle i) (hc.1 i)
    rw [dualPairing_freqSingle, dualPairing_freqSingle] at hb
    refine hb.imp (fun ⟨k, hk⟩ => ⟨k, ?_⟩) (fun ⟨k, hk⟩ => ⟨k, ?_⟩)
    · show a i - b i = (k : ℝ)
      exact hk
    · show a i + b i = (k : ℝ)
      exact hk
  · intro i j hij
    have hb := branch (freqPair i j) (hc.2 i j hij)
    rw [dualPairing_freqPair, dualPairing_freqPair] at hb
    refine hb.imp (fun ⟨k, hk⟩ => ⟨k, ?_⟩) (fun ⟨k, hk⟩ => ⟨k, ?_⟩)
    · show (a i - b i) + (a j - b j) = (k : ℝ)
      linarith
    · show (a i + b i) + (a j + b j) = (k : ℝ)
      linarith

/-- **The certificate as a splitting diagnostic**: a form whose
coordinates split with no cross terms admits no finite certificate.
Only this direction is proved; nothing here says a certificate exists
whenever no such splitting does. -/
theorem not_finiteCertificate_of_split (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) : ¬ FiniteCertificate M α := fun hc =>
  not_evenPartSeparating_of_split hM hα hT hi₀ hj₀
    (evenPartSeparating_of_finiteCertificate hM hα hc)

/-- Coprime rigidity from the finite certificate. -/
theorem gramDefect_neg_of_finiteCertificate (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (hcert : FiniteCertificate M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hβ : (0 : ℝ) < (a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s) := by positivity
  exact gramDefect_neg_of_evenPartSeparating hM hd hs ha hb hco
    (evenPartSeparating_of_finiteCertificate hM hβ hcert)

end Theaetetus
