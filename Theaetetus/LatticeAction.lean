import Theaetetus.QuadraticAction
import Theaetetus.Periodization
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The Quadratic-Lattice Action: real positivity on the bundle

The carrier bundle, rebuilt on the lattice: a
`QuadLatticeAction` is a finite free `ℤ`-module with a
symmetric bi-additive `ℝ`-valued form whose **real scalar extension**
`ℝ ⊗[ℤ] Λ` is positive definite — positivity on integral points alone
is *not* stored, because it does not suffice (a
counterexample: `B((m,n),(m',n')) = (m+√2n)(m'+√2n')` on `ℤ²` is
positive at every nonzero lattice point yet has a real null direction
and a divergent Boltzmann sum). From real positivity everything else
is **derived**:

* `form_posDef` — integral positivity, through the lattice embedding
  `a ↦ 1 ⊗ a` (injective for free modules);
* `gram_posDef` — every finite basis's Gram matrix is positive
  definite on `ℝ`;
* `summable` — the Boltzmann weight is summable, through any integral
  basis and the coordinate engine `summable_exp_neg_quadForm`;
* `bilinBaseChange_posDef_of_gram` — the converse discharge: one
  positive-definite Gram chart certifies the real extension, which is
  how `classQuadAction` (`Theaetetus/Carrier.lean`) supplies the
  field. -/

namespace Theaetetus

open scoped BigOperators TensorProduct
open Matrix

universe u

/-! ## The canonical bilinear extension to the real scalar extension -/

section BaseChange

variable {Λ : Type u} [AddCommGroup Λ] [Module ℤ Λ]

/-- Symmetric bi-additive real data on a `ℤ`-module, bundled as a
`ℤ`-bilinear map. Right-additivity is symmetry plus left-additivity;
`ℤ`-linearity of an additive map is automatic (`map_intCast_smul`),
for whichever `Module ℤ` instances are in scope. -/
noncomputable def intBilin (f : Λ → Λ → ℝ) (hcomm : ∀ a b, f a b = f b a)
    (hadd : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) :
    Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℝ where
  toFun a :=
    { toFun := f a
      map_add' := fun b₁ b₂ => by
        rw [hcomm a (b₁ + b₂), hadd b₁ b₂ a, hcomm b₁ a, hcomm b₂ a]
      map_smul' := fun n x => by
        have h := map_intCast_smul
          (AddMonoidHom.mk' (f a) fun b₁ b₂ => by
            rw [hcomm a (b₁ + b₂), hadd b₁ b₂ a, hcomm b₁ a, hcomm b₂ a])
          ℤ ℤ n x
        simpa using h }
  map_add' a₁ a₂ := LinearMap.ext fun b => hadd a₁ a₂ b
  map_smul' n a := LinearMap.ext fun b => by
    have h := map_intCast_smul
      (AddMonoidHom.mk' (fun y => f y b) fun a₁ a₂ => hadd a₁ a₂ b) ℤ ℤ n a
    simpa using h

@[simp] theorem intBilin_apply (f : Λ → Λ → ℝ) (hcomm) (hadd) (a b : Λ) :
    intBilin f hcomm hadd a b = f a b := rfl

/-- **The canonical `ℝ`-bilinear extension** of symmetric bi-additive
real data on `Λ` to the real scalar extension `ℝ ⊗[ℤ] Λ` — by the
universal property of base change (`liftBaseChange`), applied in each
slot. No basis appears. -/
noncomputable def bilinBaseChange (f : Λ → Λ → ℝ) (hcomm : ∀ a b, f a b = f b a)
    (hadd : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) :
    (ℝ ⊗[ℤ] Λ) →ₗ[ℝ] (ℝ ⊗[ℤ] Λ) →ₗ[ℝ] ℝ :=
  LinearMap.liftBaseChange ℝ
    (((LinearMap.liftBaseChangeEquiv ℝ).toLinearMap.restrictScalars ℤ).comp
      (intBilin f hcomm hadd))

@[simp] theorem bilinBaseChange_tmul (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (r s : ℝ) (a b : Λ) :
    bilinBaseChange f hcomm hadd (r ⊗ₜ a) (s ⊗ₜ b) = r * s * f a b := by
  simp only [bilinBaseChange, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.smul_apply, smul_eq_mul, intBilin_apply]
  ring

theorem bilinBaseChange_one_tmul (f : Λ → Λ → ℝ) (hcomm) (hadd) (a b : Λ) :
    bilinBaseChange f hcomm hadd ((1 : ℝ) ⊗ₜ a) ((1 : ℝ) ⊗ₜ b) = f a b := by
  rw [bilinBaseChange_tmul]
  ring

/-- The lattice embeds in its real scalar extension: `1 ⊗ a` vanishes
only at `a = 0`, read off the base-changed basis coordinates of any
`ℤ`-basis. -/
theorem one_tmul_ne_zero [Module.Free ℤ Λ] {a : Λ} (ha : a ≠ 0) :
    (1 : ℝ) ⊗ₜ[ℤ] a ≠ (0 : ℝ ⊗[ℤ] Λ) := by
  intro h0
  apply ha
  set b := Module.Free.chooseBasis ℤ Λ with hb
  apply b.repr.injective
  ext i
  have h := congrArg (fun z => (b.baseChange ℝ).repr z i) h0
  simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, zsmul_eq_mul, mul_one] at h
  rw [map_zero]
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  exact_mod_cast h

/-- The base-changed coordinates of an embedded lattice point are the
casts of its integer coordinates. -/
theorem baseChange_equivFun_one_tmul {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (x : Λ) (i : Fin n) :
    (b.baseChange ℝ).equivFun ((1 : ℝ) ⊗ₜ x) i = ((b.repr x i : ℤ) : ℝ) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    zsmul_eq_mul, mul_one]

/-- The extension in base-changed coordinates: a finite double sum
against the Gram entries of the underlying basis. -/
theorem bilinBaseChange_apply_equivFun {n : ℕ} (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (b : Module.Basis (Fin n) ℤ Λ) (x y : ℝ ⊗[ℤ] Λ) :
    bilinBaseChange f hcomm hadd x y
      = ∑ i, ∑ j, (b.baseChange ℝ).equivFun x i * (b.baseChange ℝ).equivFun y j
          * f (b i) (b j) := by
  set bR := b.baseChange ℝ with hbR
  have hx := (bR.sum_equivFun x).symm
  have hy := (bR.sum_equivFun y).symm
  have h1 : bilinBaseChange f hcomm hadd x
      = ∑ i, bR.equivFun x i • bilinBaseChange f hcomm hadd (bR i) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply]
  conv_lhs => rw [hy]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul]
  have hij : bilinBaseChange f hcomm hadd (bR i) (bR j) = f (b i) (b j) := by
    rw [hbR, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
    exact bilinBaseChange_one_tmul f hcomm hadd (b i) (b j)
  rw [hij, smul_eq_mul]

/-- **The Gram-chart discharge**: one basis whose real Gram
matrix is positive definite certifies positive-definiteness of the
whole real extension. This is how concrete carriers
(`classQuadAction`) supply the `posDef_baseChange` field. -/
theorem bilinBaseChange_posDef_of_gram {n : ℕ} (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (b : Module.Basis (Fin n) ℤ Λ)
    (hgram : (Matrix.of fun i j => f (b i) (b j)).PosDef) :
    ∀ x : ℝ ⊗[ℤ] Λ, x ≠ 0 → 0 < bilinBaseChange f hcomm hadd x x := by
  intro x hx
  set bR := b.baseChange ℝ with hbR
  set c : Fin n → ℝ := bR.equivFun x with hc
  have hcne : c ≠ 0 := by
    intro h0
    apply hx
    have := congrArg bR.equivFun.symm (hc.symm.trans h0)
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this
  have hquad : bilinBaseChange f hcomm hadd x x
      = c ⬝ᵥ (Matrix.of fun i j => f (b i) (b j)).mulVec c := by
    rw [bilinBaseChange_apply_equivFun f hcomm hadd b x x,
      ← quadForm_dotProduct]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.of_apply]
    ring
  have hpos := (posDef_iff_dotProduct_mulVec.mp hgram).2 hcne
  have hstar : star c = c := funext fun i => star_trivial _
  rw [hstar] at hpos
  rw [hquad]
  exact hpos

end BaseChange

/-! ## The bundle -/

/-- An **integral quadratic-lattice action**: a finite free `ℤ`-module
of sectors — a genuine integral lattice — with an
`ℝ`-valued symmetric bi-additive form whose **real scalar extension is
positive definite** (integral positivity is derived, never
stored, and stored summability is gone — both were assertion debt).
`toSectorAction` is the analytic projection. -/
structure QuadLatticeAction where
  /-- The sector lattice. -/
  Λ : Type u
  [addCommGroup : AddCommGroup Λ]
  [module : Module ℤ Λ]
  [free : Module.Free ℤ Λ]
  [finite : Module.Finite ℤ Λ]
  /-- The bilinear form. -/
  form : Λ → Λ → ℝ
  form_comm : ∀ a b, form a b = form b a
  form_add_left : ∀ a₁ a₂ b, form (a₁ + a₂) b = form a₁ b + form a₂ b
  /-- Positive-definiteness on the **real scalar extension** —
  integral positivity alone does not suffice. -/
  posDef_baseChange : ∀ x : ℝ ⊗[ℤ] Λ, x ≠ 0 →
    0 < bilinBaseChange form form_comm form_add_left x x

namespace QuadLatticeAction

attribute [instance] QuadLatticeAction.addCommGroup QuadLatticeAction.module
  QuadLatticeAction.free QuadLatticeAction.finite

variable (Q : QuadLatticeAction.{u})

/-- The bundled `ℤ`-bilinear form. -/
noncomputable def bilin : Q.Λ →ₗ[ℤ] Q.Λ →ₗ[ℤ] ℝ :=
  intBilin Q.form Q.form_comm Q.form_add_left

@[simp] theorem bilin_apply (a b : Q.Λ) : Q.bilin a b = Q.form a b := rfl

/-- The real scalar extension of the form — canonical, basis-free. -/
noncomputable def formExt : (ℝ ⊗[ℤ] Q.Λ) →ₗ[ℝ] (ℝ ⊗[ℤ] Q.Λ) →ₗ[ℝ] ℝ :=
  bilinBaseChange Q.form Q.form_comm Q.form_add_left

@[simp] theorem formExt_tmul (r s : ℝ) (a b : Q.Λ) :
    Q.formExt (r ⊗ₜ a) (s ⊗ₜ b) = r * s * Q.form a b :=
  bilinBaseChange_tmul _ _ _ r s a b

theorem formExt_posDef (x : ℝ ⊗[ℤ] Q.Λ) (hx : x ≠ 0) : 0 < Q.formExt x x :=
  Q.posDef_baseChange x hx

theorem form_zero_left (b : Q.Λ) : Q.form 0 b = 0 := by
  have h := Q.form_add_left 0 0 b
  rw [add_zero] at h
  linarith

/-- **Integral positivity is a theorem**: through the
lattice embedding `a ↦ 1 ⊗ a` into the real scalar extension. -/
theorem form_posDef (a : Q.Λ) (ha : a ≠ 0) : 0 < Q.form a a := by
  have h := Q.posDef_baseChange ((1 : ℝ) ⊗ₜ a) (one_tmul_ne_zero ha)
  rwa [bilinBaseChange_one_tmul] at h

theorem form_self_nonneg (a : Q.Λ) : 0 ≤ Q.form a a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Q.form_zero_left]
  · exact (Q.form_posDef a ha).le

/-! ## The Gram matrix at a finite basis -/

/-- The Gram matrix of the form at a finite basis. -/
noncomputable def gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Q.form (b i) (b j)

@[simp] theorem gram_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (i j : Fin n) : Q.gram b i j = Q.form (b i) (b j) := rfl

theorem gram_transpose {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.gram b)ᵀ = Q.gram b := by
  ext i j
  exact Q.form_comm (b j) (b i)

/-- The integral coordinate expansion of the form at any finite basis. -/
theorem form_repr {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) (x y : Q.Λ) :
    Q.form x y
      = ∑ i, ∑ j, ((b.repr x i : ℤ) : ℝ) * ((b.repr y j : ℤ) : ℝ)
          * Q.form (b i) (b j) := by
  have h := bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left b
    ((1 : ℝ) ⊗ₜ x) ((1 : ℝ) ⊗ₜ y)
  rw [bilinBaseChange_one_tmul] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [baseChange_equivFun_one_tmul, baseChange_equivFun_one_tmul]

/-- **Every Gram chart is positive definite on `ℝ`** — a theorem of the
real extension, consumed by the summability engine. -/
theorem gram_posDef {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.gram b).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun c hc => ?_⟩
  · show (Q.gram b)ᴴ = Q.gram b
    ext i j
    calc (Q.gram b)ᴴ i j = star ((Q.gram b) j i) := rfl
      _ = (Q.gram b) j i := star_trivial _
      _ = (Q.gram b) i j := Q.form_comm (b j) (b i)
  · set bR := b.baseChange ℝ with hbR
    set x : ℝ ⊗[ℤ] Q.Λ := bR.equivFun.symm c with hx
    have hxne : x ≠ 0 := by
      intro h0
      apply hc
      have := congrArg bR.equivFun (hx.symm.trans h0)
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    have hpos := Q.posDef_baseChange x hxne
    have hcoord : bR.equivFun x = c := by
      rw [hx, LinearEquiv.apply_symm_apply]
    have hquad : Q.formExt x x = c ⬝ᵥ (Q.gram b).mulVec c := by
      show bilinBaseChange Q.form Q.form_comm Q.form_add_left x x = _
      rw [bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left b x x,
        ← quadForm_dotProduct]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hbR, hcoord, gram_apply]
      ring
    have hstar : star c = c := funext fun i => star_trivial _
    rw [hstar]
    rw [← hquad]
    exact hpos

/-- **Summability is a theorem**: through any integral
basis, by the coordinate engine `summable_exp_neg_quadForm` at the
(positive-definite) Gram chart. -/
theorem summable : Summable (fun a : Q.Λ => Real.exp (-(Q.form a a))) := by
  set b := Module.finBasis ℤ Q.Λ with hb
  have hsum := summable_exp_neg_quadForm (Q.gram_posDef b)
  have h := (Equiv.summable_iff b.equivFun.toEquiv).mpr hsum
  refine h.congr fun a => ?_
  show Real.exp (-(∑ i, ∑ j, Q.gram b i j * ((b.equivFun a i : ℤ) : ℝ)
      * ((b.equivFun a j : ℤ) : ℝ))) = Real.exp (-(Q.form a a))
  congr 1
  rw [neg_inj, Q.form_repr b a a]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, gram_apply]
  ring

/-- The analytic projection: forget the lattice and the bilinear
structure, keep sectors, energies `E a := form a a`, and the sum. -/
noncomputable def toSectorAction : SectorAction.{u} where
  Λ := Q.Λ
  E := fun a => Q.form a a
  E_zero := ⟨0, by rw [Q.form_zero_left]⟩
  E_nonneg := Q.form_self_nonneg
  summable := Q.summable

/-! ### Inverse-temperature scaling on the bundle

Temperature is an operation on the carrier bundle itself:
`QuadLatticeAction.scale` multiplies the form by `β > 0`, and the
basis-free β-scaled partition function (`scaledPartFn`) reads the
Boltzmann sum of the scaled form. -/

/-- **The inverse-temperature scaling of a bundled lattice action**:
the form multiplied by `β > 0` — positive definite via
the canonical chart. -/
noncomputable def scale (β : ℝ) (hβ : 0 < β) : QuadLatticeAction.{u} where
  Λ := Q.Λ
  form a b := β * Q.form a b
  form_comm a b := by rw [Q.form_comm]
  form_add_left a₁ a₂ b := by rw [Q.form_add_left]; ring
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _ (Module.finBasis ℤ Q.Λ) ?_
    have hmat : (Matrix.of fun i j =>
          β * Q.form (Module.finBasis ℤ Q.Λ i) (Module.finBasis ℤ Q.Λ j))
        = β • Q.gram (Module.finBasis ℤ Q.Λ) := by
      ext i j
      rw [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      congr 1
    rw [hmat]
    exact posDef_smul' (Q.gram_posDef (Module.finBasis ℤ Q.Λ)) hβ

/-- The bundle's β-scaled partition function — basis-free. -/
noncomputable def scaledPartFn (β : ℝ) : ℝ :=
  ∑' a : Q.Λ, Real.exp (-(β * Q.form a a))

end QuadLatticeAction

end Theaetetus
