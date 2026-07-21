import Theaetetus.GraphHomology
import Theaetetus.CoarseGrain
import Theaetetus.Periodization
import Theaetetus.Carrier
import Mathlib.Algebra.Module.ZMod

/-! # Resolution Counting: the Keystone's Counting Shadows

The finite-resolution corollaries derived from the ℤ-form keystone
(`Theaetetus/GraphHomology.lean`). Fix a resolution `q ≥ 1`:
descriptions are cochains `G.E → ZMod q`, neighbor-local
re-descriptions are mod-`q` gradients — `G.gradLin (ZMod q)`, the
*same* graph-level gradient as the real and integer layers, defined
once. Then, through any lattice basis
`B : Module.Basis (Fin n) ℤ G.cycleLattice` (no
presentation structure, no stored fields):

* **`card_quotient`**: the compression residue counts exactly
  `q ^ b₁` — the incompressible content is `b₁` resolution-digits.

The mod-`q` layer derives entirely from the basis's theorems:
surjectivity by reducing an integer witness (`periods_onto`), and
exactness by the *lift-and-correct* argument — lift `ω` to `ℤ`
through `ZMod.val`; its integer periods are divisible by `q`, say
`q·m`; subtract `q·τ` where `τ` realizes `m`; the corrected cochain
has zero integer periods, hence an integer potential
(`integral_potentials`), and the correction vanishes mod `q`. Total
unimodularity by another name: no resolution is bad.

Beyond the counting layer: coefficient reduction `h1Res` maps the
integral carrier `H¹(G;ℤ)` onto the resolution-`q` residue, its
kernel is exactly `q·H¹(G;ℤ)` (`ker_h1Res`), so the residue **is**
`H1Reduction G q = H¹(G;ℤ) ⧸ q·H¹(G;ℤ)` (`h1ResQuotEquiv`). The
Gibbs distribution of the class action pushes through the reduction
(`residueMass`), concentrates strictly on the zero class
(`residueMass_lt_residueMass_zero`), and coarse-grains the harmonic
action (`residueAction`). For `q ∣ q'` the reductions form a tower
(`h1TowerMap`), each fiber counting `c^{b₁}` classes
(`card_h1TowerMap_fiber`). -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})
variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)
variable (q : ℕ) [NeZero q]

/-- The mod-`q` cycle basis of a lattice basis. -/
noncomputable def cyclesQ : Fin n → G.E → ZMod q :=
  fun j e => ((G.cyclesZ B j e : ℤ) : ZMod q)

private lemma cast_val_int (a : ZMod q) : ((a.val : ℤ) : ZMod q) = a := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_rightInverse a

omit [NeZero q] in
/-- Casting a dot product, in applied form: pointwise cast
compatibility on both factors transfers the product. -/
private lemma dot_cast_eq (x y : G.E → ℤ) (x' y' : G.E → ZMod q)
    (hx : ∀ e, ((x e : ℤ) : ZMod q) = x' e)
    (hy : ∀ e, ((y e : ℤ) : ZMod q) = y' e) :
    ((x ⬝ᵥ y : ℤ) : ZMod q) = x' ⬝ᵥ y' := by
  show ((∑ e, x e * y e : ℤ) : ZMod q) = ∑ e, x' e * y' e
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hx e, hy e]

/-- Mod-`q` Stokes: mod-`q` gradients have zero mod-`q` periods.
Derived from integer Stokes by lifting the potential. -/
theorem gradQ_period (g : G.V → ZMod q) (j : Fin n) :
    G.grad g ⬝ᵥ G.cyclesQ B q j = 0 := by
  show (fun e => g (G.tgt e) - g (G.src e)) ⬝ᵥ G.cyclesQ B q j = 0
  have hint : (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
      ⬝ᵥ G.cyclesZ B j = 0 :=
    G.gradZ_period B (fun v => ((g v).val : ℤ)) j
  have hdot := G.dot_cast_eq (q := q)
    (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
    (G.cyclesZ B j)
    (fun e => g (G.tgt e) - g (G.src e))
    (G.cyclesQ B q j)
    (fun e => by rw [Int.cast_sub, cast_val_int, cast_val_int])
    (fun e => rfl)
  rw [← hdot, hint, Int.cast_zero]

/-- Mod-`q` period realizability, by reducing an integer witness. -/
theorem periodsQ_onto (k : Fin n → ZMod q) :
    ∃ ω : G.E → ZMod q, ∀ j, ω ⬝ᵥ G.cyclesQ B q j = k j := by
  obtain ⟨ωZ, hω⟩ := G.periods_onto B (fun j => ((k j).val : ℤ))
  refine ⟨fun e => ((ωZ e : ℤ) : ZMod q), fun j => ?_⟩
  have hdot := G.dot_cast_eq (q := q) ωZ (G.cyclesZ B j)
    (fun e => ((ωZ e : ℤ) : ZMod q)) (G.cyclesQ B q j)
    (fun e => rfl) (fun e => rfl)
  rw [← hdot, hω j]
  exact cast_val_int q (k j)

/-- **Mod-`q` exactness by lift-and-correct**: a mod-`q` cochain with
zero mod-`q` periods is a mod-`q` gradient. -/
theorem exists_potentialQ (ω : G.E → ZMod q)
    (h : ∀ j, ω ⬝ᵥ G.cyclesQ B q j = 0) :
    ∃ g : G.V → ZMod q, G.grad g = ω := by
  -- Lift to ℤ.
  set ωZ : G.E → ℤ := fun e => ((ω e).val : ℤ) with hωZ
  -- Integer periods are divisible by q.
  have hdvd : ∀ j, (q : ℤ) ∣ ωZ ⬝ᵥ G.cyclesZ B j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hdot := G.dot_cast_eq (q := q) ωZ (G.cyclesZ B j) ω (G.cyclesQ B q j)
      (fun e => cast_val_int q (ω e)) (fun e => rfl)
    rw [hdot]
    exact h j
  choose m hm using hdvd
  -- Correct by an integer realization of m.
  obtain ⟨τ, hτ⟩ := G.periods_onto B m
  have hper : ∀ j, (fun e => ωZ e - q * τ e) ⬝ᵥ G.cyclesZ B j = 0 := by
    intro j
    have hsplit : (fun e => ωZ e - q * τ e) ⬝ᵥ G.cyclesZ B j
        = ωZ ⬝ᵥ G.cyclesZ B j - q * (τ ⬝ᵥ G.cyclesZ B j) := by
      show ∑ e, (ωZ e - q * τ e) * G.cyclesZ B j e = _
      rw [show (∑ e, (ωZ e - q * τ e) * G.cyclesZ B j e)
          = ∑ e, (ωZ e * G.cyclesZ B j e - q * (τ e * G.cyclesZ B j e)) from
        Finset.sum_congr rfl fun e _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    rw [hsplit, hτ j, hm j]
    ring
  obtain ⟨g, hg⟩ := G.integral_potentials B (fun e => ωZ e - q * τ e) hper
  refine ⟨fun v => ((g v : ℤ) : ZMod q), funext fun e => ?_⟩
  have hge : g (G.tgt e) - g (G.src e) = ωZ e - q * τ e := congrFun hg e
  show ((g (G.tgt e) : ℤ) : ZMod q) - ((g (G.src e) : ℤ) : ZMod q) = ω e
  rw [← Int.cast_sub, hge, Int.cast_sub, Int.cast_mul,
    show ((q : ℤ) : ZMod q) = 0 from by
      push_cast
      exact ZMod.natCast_self q,
    zero_mul, sub_zero]
  exact cast_val_int q (ω e)

/-! ## The quotient at resolution `q` -/

/-- The mod-`q` period map as a linear map. -/
noncomputable def periodLinQ :
    (G.E → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) where
  toFun ω := fun j => ω ⬝ᵥ G.cyclesQ B q j
  map_add' ω η := funext fun j => add_dotProduct ω η (G.cyclesQ B q j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (G.cyclesQ B q j)

theorem range_gradLinQ_eq_ker_periodLinQ :
    LinearMap.range (G.gradLin (ZMod q))
      = LinearMap.ker (G.periodLinQ B q) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact G.gradQ_period B q g j
  · intro h
    exact G.exists_potentialQ B q ω (fun j => congrFun h j)

theorem periodLinQ_surjective : Function.Surjective (G.periodLinQ B q) := by
  intro k
  obtain ⟨ω, hω⟩ := G.periodsQ_onto B q k
  exact ⟨ω, funext hω⟩

/-- The keystone at resolution `q`: mod-`q` descriptions modulo
mod-`q` local re-description are the mod-`q` period space. The
quotient depends only on the graph. -/
noncomputable def latticeQuotEquivQ :
    ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      ≃ₗ[ZMod q] (Fin n → ZMod q) :=
  (Submodule.quotEquivOfEq _ _
    (G.range_gradLinQ_eq_ker_periodLinQ B q)).trans
    ((G.periodLinQ B q).quotKerEquivOfSurjective
      (G.periodLinQ_surjective B q))

/-! ## The counting shadow -/

include B in
/-- **The residue counts `q ^ n` (= `q ^ b₁`)**: at any
resolution, the incompressible content of a description is exactly
`b₁` resolution-digits. -/
theorem card_quotient :
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ n := by
  rw [Nat.card_congr (G.latticeQuotEquivQ B q).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **`card_quotient` for every finite graph**: at every resolution
`q ≥ 1`, the compression residue counts exactly `q ^ b₁` — through the
fundamental basis, with no per-graph hypotheses. -/
theorem card_quotient_eq :
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ G.b1 :=
  G.card_quotient G.cycleBasis q

/-- The description quotient at a positive resolution is finite. -/
noncomputable instance descQuotFintype :
    Fintype ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  haveI : Finite ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  Fintype.ofFinite _

/-! ## The finite reduction of the intrinsic carrier

The residue is the **finite reduction of the one integral
carrier**. The intrinsic carrier's lattice is
`H¹(G;ℤ) = (G.E → ℤ) ⧸ range ∂ᵀℤ` (the sector lattice of
`classSectorAction`, `Theaetetus/Carrier.lean`, definitionally).
Coefficient reduction `h1Res` maps it onto the resolution-`q`
residue, its kernel is exactly `q·H¹(G;ℤ)` (`ker_h1Res`), so the
residue **is** `H¹(G;ℤ) ⧸ q·H¹(G;ℤ)` (`h1ResQuotEquiv`), and the
coordinates commute with the keystones
(`latticeQuotEquivQ_h1Res`). -/

omit [NeZero q] in
/-- Componentwise mod-`q` reduction of integer cochains, landing in
the resolution-`q` description quotient. -/
noncomputable def cochainResHom :
    (G.E → ℤ) →+ ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) where
  toFun τ := Submodule.Quotient.mk (fun e => ((τ e : ℤ) : ZMod q))
  map_zero' := by
    rw [show (fun e => (((0 : G.E → ℤ) e : ℤ) : ZMod q))
        = (0 : G.E → ZMod q) from funext fun e => by
      show ((0 : ℤ) : ZMod q) = 0
      exact Int.cast_zero]
    rfl
  map_add' τ σ := by
    rw [show (fun e => (((τ + σ) e : ℤ) : ZMod q))
        = (fun e => ((τ e : ℤ) : ZMod q)) + fun e => ((σ e : ℤ) : ZMod q) from
      funext fun e => by
        show ((τ e + σ e : ℤ) : ZMod q) = ((τ e : ℤ) : ZMod q) + ((σ e : ℤ) : ZMod q)
        push_cast
        rfl]
    exact Submodule.Quotient.mk_add _

omit [NeZero q] in
/-- Gradients reduce to gradients, so the reduction descends to the
intrinsic carrier's lattice `H¹(G;ℤ)`. -/
noncomputable def h1Res :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
      ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  Submodule.liftQ _ (G.cochainResHom q).toIntLinearMap (by
    rintro τ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (fun e => (((G.gradLin ℤ g) e : ℤ) : ZMod q))
      = (0 : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨fun v => ((g v : ℤ) : ZMod q), ?_⟩
    funext e
    show ((g (G.tgt e) : ℤ) : ZMod q) - ((g (G.src e) : ℤ) : ZMod q)
      = ((g (G.tgt e) - g (G.src e) : ℤ) : ZMod q)
    push_cast
    rfl)

omit [NeZero q] in
theorem h1Res_mk (τ : G.E → ℤ) :
    G.h1Res q (Submodule.Quotient.mk τ)
      = Submodule.Quotient.mk (fun e => ((τ e : ℤ) : ZMod q)) := rfl

/-- The reduction is surjective: every mod-`q` class lifts through
`ZMod.val`. -/
theorem h1Res_surjective : Function.Surjective (G.h1Res q) := by
  intro x
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨Submodule.Quotient.mk (fun e => ((ω e).val : ℤ)), ?_⟩
  rw [G.h1Res_mk q]
  exact congrArg _ (funext fun e => cast_val_int q (ω e))

/-- **The identification with the resolution keystone**: reducing a
class and reading mod-`q` coordinates equals reading integer
coordinates and reducing them — the square with `latticeQuotEquiv`
and `latticeQuotEquivQ` commutes, for every basis. -/
theorem latticeQuotEquivQ_h1Res
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.latticeQuotEquivQ B q (G.h1Res q κ)
      = fun j => (((G.latticeQuotEquiv B κ) j : ℤ) : ZMod q) := by
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  funext j
  show (fun e => ((τ e : ℤ) : ZMod q)) ⬝ᵥ G.cyclesQ B q j
    = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ZMod q)
  exact (G.dot_cast_eq q τ (G.cyclesZ B j)
    (fun e => ((τ e : ℤ) : ZMod q)) (G.cyclesQ B q j)
    (fun e => rfl) (fun e => rfl)).symm

/-- **The kernel is exactly `q·H¹(G;ℤ)`**: the reduction kills
precisely the `q`-th multiples of the integral carrier. -/
theorem ker_h1Res :
    LinearMap.ker (G.h1Res q)
      = LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))) := by
  ext κ
  constructor
  · intro hκ
    rw [LinearMap.mem_ker] at hκ
    have hsq := G.latticeQuotEquivQ_h1Res G.cycleBasis q κ
    rw [hκ, map_zero] at hsq
    have hx : ∀ j, ((G.latticeQuotEquiv G.cycleBasis κ j : ℤ) : ZMod q) = 0 :=
      fun j => (congrFun hsq.symm j).symm ▸ rfl
    have hdvd : ∀ j, (q : ℤ) ∣ G.latticeQuotEquiv G.cycleBasis κ j := by
      intro j
      have h := hx j
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    choose y hy using hdvd
    rw [LinearMap.mem_range]
    refine ⟨(G.latticeQuotEquiv G.cycleBasis).symm y, ?_⟩
    show (q : ℤ) • ((G.latticeQuotEquiv G.cycleBasis).symm y) = κ
    apply (G.latticeQuotEquiv G.cycleBasis).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext j
    show (q : ℤ) • y j = G.latticeQuotEquiv G.cycleBasis κ j
    rw [smul_eq_mul]
    exact (hy j).symm
  · rintro ⟨κ', hκ'⟩
    rw [LinearMap.mem_ker, ← hκ']
    show G.h1Res q ((q : ℤ) • κ') = 0
    rw [map_smul]
    generalize G.h1Res q κ' = x
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hω : (q : ℤ) • ω = (0 : G.E → ZMod q) := by
      funext e
      show (q : ℤ) • ω e = 0
      rw [zsmul_eq_mul,
        show ((q : ℤ) : ZMod q) = 0 from by
          push_cast
          exact ZMod.natCast_self q,
        zero_mul]
    calc (q : ℤ) • (Submodule.Quotient.mk ω :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        = Submodule.Quotient.mk ((q : ℤ) • ω) :=
          (map_zsmul (Submodule.mkQ _) _ _).symm
      _ = Submodule.Quotient.mk (0 : G.E → ZMod q) := by rw [hω]
      _ = 0 := rfl

/-- **THE FINITE REDUCTION OF THE INTRINSIC CARRIER**: the
resolution-`q` residue is exactly the integral
carrier's quotient by `q` — `H¹(G;ℤ) ⧸ q·H¹(G;ℤ) ≃ H¹(G;ZMod q)`.
One integral carrier; its finite reductions. -/
noncomputable def h1ResQuotEquiv :
    (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))))
      ≃ₗ[ℤ] ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  (Submodule.quotEquivOfEq _ _ (G.ker_h1Res q).symm).trans
    ((G.h1Res q).quotKerEquivOfSurjective (G.h1Res_surjective q))

noncomputable instance h1ReductionFintype :
    Fintype (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))) :=
  Fintype.ofEquiv _ (G.h1ResQuotEquiv q).toEquiv.symm

/-- **The finite reduction of the intrinsic carrier, named**:
`H¹(G;ℤ) ⧸ q·H¹(G;ℤ)`. -/
abbrev H1Reduction (q : ℕ) [NeZero q] : Type v :=
  ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
    ⧸ LinearMap.range ((q : ℤ) •
      (LinearMap.id :
        ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))

theorem card_H1Reduction : Nat.card (H1Reduction G q) = q ^ G.b1 := by
  rw [Nat.card_congr (G.h1ResQuotEquiv q).toEquiv, G.card_quotient_eq q]

/-! ## The Gibbs distribution through the reduction

The intrinsic Gibbs distribution of `classSectorAction`
(`Theaetetus/Carrier.lean`) is pushed through
`H¹(G;ℤ) → H1Reduction G q`: `residueMass` is the total Gibbs mass
of the integral classes over each finite sector, computed by every
basis chart (`residueMass_chart` — basis independence), and strictly
concentrated on the zero class
(`residueMass_lt_residueMass_zero`). -/

/-- **The residue distribution**: the total intrinsic
Gibbs mass of the integral classes reducing to a given finite sector
of the carrier. -/
noncomputable def residueMass (ξ : H1Reduction G q) : ℝ :=
  ∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
    (G.classSectorAction).gibbsMass κ.val

/-- **Basis independence**: every lattice basis computes
the residue distribution — the `B`-coordinate Boltzmann sum over the
coset of coordinates reducing to `ξ`, divided by the graph's partition
function. The statement's left side never mentions a basis. -/
theorem residueMass_chart {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (ξ : H1Reduction G q) :
    G.residueMass q ξ
      = (∑' k : {k : Fin n → ℤ //
            (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k)
              : H1Reduction G q) = ξ},
          Real.exp (-(G.basisGramData B).energy k.val)) / G.partFn := by
  have h1 : ∀ κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
      (G.classSectorAction).gibbsMass κ.val
        = Real.exp (-(G.harmonicEnergy κ.val)) / G.partFn := by
    intro κ
    show (G.classSectorAction).weight κ.val / (G.classSectorAction).partFn = _
    rw [G.classSectorAction_partFn]
    rfl
  rw [residueMass, tsum_congr h1, tsum_div_const]
  congr 1
  rw [← Equiv.tsum_eq (Equiv.subtypeEquiv
      ((G.latticeQuotEquiv B).toEquiv.symm) (fun k => Iff.rfl))
    (fun κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
        (Submodule.Quotient.mk κ : H1Reduction G q) = ξ} =>
      Real.exp (-(G.harmonicEnergy κ.val)))]
  refine tsum_congr fun k => ?_
  congr 1
  rw [neg_inj]
  have h := G.basisGramData_energy_latticeQuot B
    ((G.latticeQuotEquiv B).symm k.val)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-! ### The zero class is strictly modal

The quadratic action **concentrates** the residue distribution: the
zero class carries strictly more mass than every other class. In a
lattice chart the fiber over a class is a coset `k₀ + q·ℤⁿ`, its
Boltzmann sum is the Gaussian periodization of the harmonic Gram at
the fractional shift `k₀/q` (`residueMass_mk_eq_periodization`), and
a nonzero class forces a non-integer coordinate of the shift — where
the strict modal bound of the shifted Fourier expansion applies
(`periodization_lt_periodization_zero`,
`Theaetetus/Periodization.lean`). -/

/-- The residue mass of a charted class is the Gaussian periodization
of the scaled harmonic Gram at the fractional shift of any integer
representative, over the graph's partition function. -/
private lemma residueMass_mk_eq_periodization {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (k₀ : Fin n → ℤ) :
    G.residueMass q
        (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀))
      = periodization
          ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • (gramOf (G.cyclesR B))⁻¹)
          (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) / G.partFn := by
  classical
  rw [G.residueMass_chart q B]
  congr 1
  -- membership of the coset translates
  have hmem : ∀ c : Fin n → ℤ,
      (Submodule.Quotient.mk
          ((G.latticeQuotEquiv B).symm (k₀ + (q : ℤ) • c))
        : H1Reduction G q)
        = Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀) := by
    intro c
    rw [Submodule.Quotient.eq]
    refine LinearMap.mem_range.mpr ⟨(G.latticeQuotEquiv B).symm c, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
    abel
  -- the coset reindex `c ↦ k₀ + q·c` is a bijection onto the fiber
  have hbij : Function.Bijective (fun c : Fin n → ℤ =>
      (⟨k₀ + (q : ℤ) • c, hmem c⟩ : {k : Fin n → ℤ //
        (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k)
          : H1Reduction G q)
          = Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀)})) := by
    constructor
    · intro c c' hcc'
      have h2 : (q : ℤ) • c = (q : ℤ) • c' :=
        add_left_cancel (congrArg Subtype.val hcc')
      exact smul_right_injective _
        (by exact_mod_cast (NeZero.ne q) : (q : ℤ) ≠ 0) h2
    · rintro ⟨k, hk⟩
      rw [Submodule.Quotient.eq] at hk
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
      rw [LinearMap.smul_apply, LinearMap.id_apply] at hy
      refine ⟨G.latticeQuotEquiv B y, ?_⟩
      apply Subtype.ext
      show k₀ + (q : ℤ) • (G.latticeQuotEquiv B) y = k
      have h3 := congrArg (G.latticeQuotEquiv B) hy
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h3
      rw [h3]
      abel
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)]
  simp only [periodization]
  refine tsum_congr fun c => ?_
  set A : Matrix (Fin n) (Fin n) ℝ := (gramOf (G.cyclesR B))⁻¹ with hA
  set y : Fin n → ℝ :=
    (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) + fun i => (c i : ℝ) with hy
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hvec : (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ))
      = ((q : ℕ) : ℝ) • y := by
    funext i
    show (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)
      = ((q : ℕ) : ℝ) * ((k₀ i : ℝ) / ((q : ℕ) : ℝ) + (c i : ℝ))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have henergy : (G.basisGramData B).energy
        ((Equiv.ofBijective _ hbij c).val)
      = (((q : ℕ) : ℝ) • y) ⬝ᵥ A.mulVec (((q : ℕ) : ℝ) • y) := by
    have h1 : (G.basisGramData B).energy (k₀ + (q : ℤ) • c)
        = (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)) ⬝ᵥ
            A.mulVec (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)) := by
      show ∑ i, ∑ j, A i j * (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)
          * (((k₀ + (q : ℤ) • c) j : ℤ) : ℝ) = _
      exact quadForm_dotProduct A _
    rw [show (Equiv.ofBijective _ hbij c).val = k₀ + (q : ℤ) • c from rfl,
      h1, hvec]
  show Real.exp (-(G.basisGramData B).energy ((Equiv.ofBijective _ hbij c).val))
    = gaussian ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A)
        ((fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) + fun i => (c i : ℝ))
  rw [henergy]
  show Real.exp (-((((q : ℕ) : ℝ) • y) ⬝ᵥ A.mulVec (((q : ℕ) : ℝ) • y)))
    = Real.exp (-Real.pi
        * (y ⬝ᵥ (((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A).mulVec y)))
  congr 1
  rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp

/-- **The zero class is strictly modal**: every nonzero
finite sector carries strictly less residue mass than the zero
sector — the quadratic action genuinely concentrates the residue
distribution. -/
theorem residueMass_lt_residueMass_zero {ξ : H1Reduction G q}
    (hξ : ξ ≠ 0) : G.residueMass q ξ < G.residueMass q 0 := by
  classical
  obtain ⟨κ₀, hκ₀⟩ := Submodule.Quotient.mk_surjective _ ξ
  set k₀ : Fin G.b1 → ℤ := G.latticeQuotEquiv G.cycleBasis κ₀ with hk₀
  have hmkξ : (Submodule.Quotient.mk
      ((G.latticeQuotEquiv G.cycleBasis).symm k₀) : H1Reduction G q) = ξ := by
    rw [hk₀, LinearEquiv.symm_apply_apply, hκ₀]
  -- a nonzero class has a representative coordinate `q` does not divide
  have hcoord : ∃ i, ¬ ((q : ℤ) ∣ k₀ i) := by
    by_contra hall
    push_neg at hall
    apply hξ
    choose f hf using fun i => hall i
    have hk : k₀ = (q : ℤ) • f := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact hf i
    rw [← hmkξ, hk, map_smul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr
      ⟨(G.latticeQuotEquiv G.cycleBasis).symm f, by
        rw [LinearMap.smul_apply, LinearMap.id_apply]⟩
  obtain ⟨i₀, hi₀⟩ := hcoord
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  set A : Matrix (Fin G.b1) (Fin G.b1) ℝ :=
    (gramOf (G.cyclesR G.cycleBasis))⁻¹ with hA
  have hApos : A.PosDef := posDef_inv (G.gramOf_cyclesR_posDef G.cycleBasis)
  have hMq : ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A).PosDef :=
    posDef_smul' hApos (div_pos (pow_pos hq0 2) Real.pi_pos)
  -- both masses, as periodizations
  have hmass0 : G.residueMass q 0
      = periodization ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A) 0 / G.partFn := by
    have h := G.residueMass_mk_eq_periodization q G.cycleBasis 0
    rw [map_zero] at h
    rw [show (Submodule.Quotient.mk (0 : (G.E → ℤ) ⧸
        LinearMap.range (G.gradLin ℤ)) : H1Reduction G q) = 0 from rfl] at h
    simp only [Pi.zero_apply, Int.cast_zero, zero_div] at h
    exact h
  have hmassξ : G.residueMass q ξ
      = periodization ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A)
          (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) / G.partFn := by
    have h := G.residueMass_mk_eq_periodization q G.cycleBasis k₀
    rw [hmkξ] at h
    exact h
  -- the fractional shift misses the integers at `i₀`
  have hx : ∀ z : ℤ, (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) i₀ ≠ (z : ℝ) := by
    intro z hz
    apply hi₀
    refine ⟨z, ?_⟩
    have h1 : (k₀ i₀ : ℝ) = (z : ℝ) * ((q : ℕ) : ℝ) :=
      (div_eq_iff (ne_of_gt hq0)).mp hz
    exact_mod_cast h1.trans (mul_comm _ _)
  -- the graph's partition function is positive
  have hZ : 0 < G.partFn := by
    have h := (G.classSectorAction).partFn_pos
    rwa [G.classSectorAction_partFn] at h
  rw [hmassξ, hmass0]
  exact (div_lt_div_iff_of_pos_right hZ).mpr
    (periodization_lt_periodization_zero hMq hx)

/-! ### The residue action: coarse-graining the harmonic action

The residue distribution is the Gibbs law of an action — and the
action itself is the **coarse-graining of the harmonic action**, not
a reconstruction from the normalized masses. The **unnormalized coset
weight** `W ξ = ∑_{κ mod q = ξ} exp(−harmonicEnergy κ)`
(`residueWeight`) satisfies `residueMass ξ = W ξ / Z`
(`residueMass_eq_residueWeight_div`); the **residue action** is
`classSectorAction.coarseGrain` at the quotient map, the partition
function factorizes as `Z = W 0 · Z_residue`
(`classPartFn_eq_residueWeight_mul`), and the complexity decomposes
(`classComplexity_residue_split`). -/

/-- The residue mass is maximal at the zero class — the weak form of
the strict modal bound. -/
theorem residueMass_le_residueMass_zero (ξ : H1Reduction G q) :
    G.residueMass q ξ ≤ G.residueMass q 0 := by
  by_cases hξ : ξ = 0
  · rw [hξ]
  · exact (G.residueMass_lt_residueMass_zero q hξ).le

/-- **The unnormalized coset weight**:
`W ξ = ∑_{κ mod q = ξ} exp(−harmonicEnergy κ)` — the harmonic
action's coarse weight at the quotient map onto the finite
reduction. -/
noncomputable def residueWeight (ξ : H1Reduction G q) : ℝ :=
  (G.classSectorAction).coarseWeight
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q)) ξ

/-- Every coset weight is positive — the fiber is nonempty. -/
theorem residueWeight_pos (ξ : H1Reduction G q) :
    0 < G.residueWeight q ξ := by
  obtain ⟨κ₀, hκ₀⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact SectorAction.coarseWeight_pos (G.classSectorAction) ⟨κ₀, hκ₀⟩

/-- **The residue mass is the coset weight over the partition
function**: the normalized masses of `residueMass` are
the coarse Boltzmann weights of the harmonic action, divided by its
partition function. -/
theorem residueMass_eq_residueWeight_div (ξ : H1Reduction G q) :
    G.residueMass q ξ
      = G.residueWeight q ξ / (G.classSectorAction).partFn := by
  show (∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
    (G.classSectorAction).weight κ.val / (G.classSectorAction).partFn) = _
  rw [tsum_div_const]
  rfl

/-- The zero coset is modal at the weight level. -/
theorem residueWeight_le_residueWeight_zero (ξ : H1Reduction G q) :
    G.residueWeight q ξ ≤ G.residueWeight q 0 := by
  have hZ : (0 : ℝ) < (G.classSectorAction).partFn :=
    (G.classSectorAction).partFn_pos
  have h := G.residueMass_le_residueMass_zero q ξ
  rw [G.residueMass_eq_residueWeight_div q ξ,
    G.residueMass_eq_residueWeight_div q 0] at h
  have h2 := mul_le_mul_of_nonneg_right h hZ.le
  rwa [div_mul_cancel₀ _ hZ.ne', div_mul_cancel₀ _ hZ.ne'] at h2

/-- **The residue action**: the coarse-graining of
the harmonic action at the quotient map onto the finite reduction —
the generic `SectorAction.coarseGrain`, with the zero class as the
modal ground state. Its energy is the coset free-energy difference,
its partition function divides the harmonic one, and its Gibbs mass
is the residue distribution. -/
noncomputable def residueAction : SectorAction.{v} :=
  (G.classSectorAction).coarseGrain
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q)) 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-- **The harmonic partition function factorizes through the residue
action**: `Z = W 0 · Z_residue`. -/
theorem classPartFn_eq_residueWeight_mul :
    (G.classSectorAction).partFn
      = G.residueWeight q 0 * (G.residueAction q).partFn :=
  SectorAction.partFn_eq_coarseWeight_mul (G.classSectorAction) _ 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-- **The harmonic complexity decomposes through the residue action**: `log Z = log W 0 + K(residueAction)`. -/
theorem classComplexity_residue_split :
    (G.classSectorAction).complexity
      = Real.log (G.residueWeight q 0) + (G.residueAction q).complexity :=
  SectorAction.complexity_eq_coarseGrain (G.classSectorAction) _ 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-! ### The resolution tower

Coarse-grainings at different resolutions are not disconnected
snapshots: for `q ∣ q'` the finer reduction `H¹⧸q'H¹` maps
canonically onto the coarser `H¹⧸qH¹` (`h1TowerMap`), surjectively
(`h1TowerMap_surjective`). -/

section Tower

variable (q' : ℕ) [NeZero q']

omit [NeZero q] [NeZero q'] in
private lemma range_qsmul_le (hdvd : q ∣ q') :
    LinearMap.range ((q' : ℤ) •
        (LinearMap.id :
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))
      ≤ LinearMap.range ((q : ℤ) •
        (LinearMap.id :
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨(c : ℤ) • y, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, show ((q : ℤ)) * (c : ℤ) = ((q' : ℤ)) from by
    exact_mod_cast hc.symm]

/-- **The canonical reduction between resolutions**: for
`q ∣ q'`, the finer reduction `H¹⧸q'H¹` maps onto the coarser
`H¹⧸qH¹` — the identity of the carrier, descended to the
quotients. -/
noncomputable def h1TowerMap (hdvd : q ∣ q') :
    H1Reduction G q' →ₗ[ℤ] H1Reduction G q :=
  Submodule.mapQ _ _ LinearMap.id (G.range_qsmul_le q q' hdvd)

/-- **Surjectivity**: every coarse class is hit — both
reductions are quotients of the same carrier. -/
theorem h1TowerMap_surjective (hdvd : q ∣ q') :
    Function.Surjective (G.h1TowerMap q q' hdvd) := by
  intro ξ
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact ⟨Submodule.Quotient.mk κ, rfl⟩

end Tower

/-! ### The price of resolution loss

The tower is not free: dropping from resolution `q' = c·q` to
resolution `q` merges `c^{b₁}` fine classes into each coarse class
(`card_h1TowerMap_fiber`). -/

section TowerCost

variable (q' c : ℕ) [NeZero q']

private noncomputable def towerFiberEquivKer (hdvd : q ∣ q') (ξ : H1Reduction G q)
    (η₀ : H1Reduction G q') (hη₀ : G.h1TowerMap q q' hdvd η₀ = ξ) :
    {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ}
      ≃ {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = 0} where
  toFun η := ⟨η.val - η₀, by rw [map_sub, η.prop, hη₀, sub_self]⟩
  invFun η := ⟨η.val + η₀, by rw [map_add, η.prop, hη₀, zero_add]⟩
  left_inv η := Subtype.ext (sub_add_cancel _ _)
  right_inv η := Subtype.ext (add_sub_cancel_right _ _)

/-- **Every tower fiber has `c^{b₁}` classes**: dropping
one resolution step `q' = c·q` merges exactly `c^{b₁}` fine classes
into each coarse class. -/
theorem card_h1TowerMap_fiber (hdvd : q ∣ q') (hq' : q' = c * q)
    (ξ : H1Reduction G q) :
    Nat.card {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ}
      = c ^ G.b1 := by
  classical
  have hfib : ∀ ζ : H1Reduction G q,
      Nat.card {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ζ}
        = Nat.card {η : H1Reduction G q' //
            G.h1TowerMap q q' hdvd η = 0} := by
    intro ζ
    obtain ⟨η₁, hη₁⟩ := G.h1TowerMap_surjective q q' hdvd ζ
    exact Nat.card_congr (G.towerFiberEquivKer q q' hdvd ζ η₁ hη₁)
  have htot := card_eq_card_mul_of_fiber
    (fun η : H1Reduction G q' => G.h1TowerMap q q' hdvd η) hfib
  have hq : Nat.card (H1Reduction G q) = q ^ G.b1 := G.card_H1Reduction q
  have hq'' : Nat.card (H1Reduction G q') = q' ^ G.b1 :=
    G.card_H1Reduction q'
  rw [Nat.card_eq_fintype_card] at hq hq''
  rw [hq'', hq] at htot
  have hpow : q' ^ G.b1 = c ^ G.b1 * q ^ G.b1 := by
    rw [hq', mul_pow]
  have hqpos : 0 < q ^ G.b1 :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _
  have hm : Nat.card {η : H1Reduction G q' //
      G.h1TowerMap q q' hdvd η = 0} = c ^ G.b1 := by
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc q ^ G.b1 * Nat.card {η : H1Reduction G q' //
          G.h1TowerMap q q' hdvd η = 0}
        = q' ^ G.b1 := htot.symm
      _ = c ^ G.b1 * q ^ G.b1 := hpow
      _ = q ^ G.b1 * c ^ G.b1 := mul_comm _ _
  rw [hfib ξ, hm]

end TowerCost

end IncidenceGraph

end Theaetetus
