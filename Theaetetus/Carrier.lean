import Theaetetus.Periods
import Theaetetus.LatticeAction

/-! # The Intrinsic Harmonic Energy and the Intrinsic Carrier

**Harmonic theory for every finite graph, on the intrinsic classes.**
The presentation is a lattice basis
`B : Module.Basis (Fin n) ℤ G.cycleLattice`;
its **priced Gram data** `basisGramData B` is the inverse of the
derived unit-edge chain Gram (the canonical pricing, with nothing
stored). `IncidenceGraph.harmonicEnergy` assigns
to each class of `H¹(G;ℤ) = (G.E → ℤ) ⧸ range ∂ᵀℤ` the energy of its
harmonic representative — defined through the fundamental basis, and
computed by **every** basis (`energy_eq_harmonicEnergy`,
`basisGramData_energy_latticeQuot`).

The load-bearing characterization (`periods_eq_cast_iff`): a real
cochain has the periods of an integer cochain `τ` — against *any*
basis — iff it is `τ̂ + grad f` for some potential. Realizing a class
is basis-independent, so the variational sets coincide, and
`IsLeast.unique` transports the energies. No coordinate transport, no
`GL(r,ℤ)` matrices in the proof.

This file provides:

* `harmonicEnergy` — basis-free by construction on the intrinsic
  quotient; basis-independent by `energy_eq_harmonicEnergy`.
* `harmonicEnergy_isLeast` — the variational identity for every
  finite graph: the class energy is the least cochain energy among
  realizers, attained.
* `harmonicEnergy_pos` — nonzero classes have positive energy,
  intrinsically.
* `partFn` — the partition function of the graph, with every basis's
  Boltzmann sum equal to the intrinsic class sum
  (`basisGramData_partFn_eq_tsum_classes`).
* `classQuadAction` / `classSectorAction` — the intrinsic carrier:
  the lattice `H¹(G;ℤ)` with the polarized form `classForm`, and its
  analytic projection.
* `classQuadActionβ` / `classSectorActionβ` / `classScaledPartFn` —
  the inverse-temperature scaling of the carrier and its β-scaled
  partition function, with the cumulant reading
  (`log_classScaledPartFn_eq_cgf`). -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

section HarmonicEnergy

variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)

/-- **The priced Gram data of a lattice basis**: the inverse of the
derived unit-edge chain Gram, with the
variational identity as a theorem
(`HarmonicGramData.ofCycles_energy_isLeast`). Nothing is stored: the
Gram and its positivity are theorems of the basis. -/
noncomputable def basisGramData : HarmonicGramData G.V :=
  HarmonicGramData.ofCycles (G.cyclesR B) (G.gramOf_cyclesR_posDef B)

/-- Casting an integer cochain's periods: `⟨τ̂, ĉⱼ⟩ = ⟨τ, cⱼ⟩` as
reals. -/
theorem cast_periods (τ : G.E → ℤ) (j : Fin n) :
    (fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ G.cyclesR B j
      = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ℝ) := by
  show ∑ e, ((τ e : ℤ) : ℝ) * G.cyclesR B j e
    = ((∑ e, τ e * G.cyclesZ B j e : ℤ) : ℝ)
  push_cast
  rfl

/-- **Realizing is basis-independent**: a real cochain has the periods
of the integer cochain `τ` against `B`'s basis iff it is `τ̂ + grad f`
— a condition with no basis in it. -/
theorem periods_eq_cast_iff (τ : G.E → ℤ) (ω : G.E → ℝ) :
    (∀ j, ω ⬝ᵥ G.cyclesR B j = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ℝ))
      ↔ ∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f := by
  constructor
  · intro hper
    have hzero : ∀ j,
        (ω - fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ G.cyclesR B j = 0 := by
      intro j
      rw [sub_dotProduct, hper j, G.cast_periods B τ j]
      ring
    obtain ⟨f, hf⟩ :=
      (G.period_eq_zero_iff_exists_grad B _).mp hzero
    refine ⟨f, ?_⟩
    rw [hf]
    funext e
    show ω e = ((τ e : ℤ) : ℝ) + (ω e - ((τ e : ℤ) : ℝ))
    ring
  · rintro ⟨f, rfl⟩
    intro j
    rw [add_dotProduct, G.cast_periods B τ j, G.grad_period B f j]
    ring

/-- Any basis's energy at the periods of `τ` is the least energy over
the basis-free realizer set `{τ̂ + grad f}`. -/
theorem isLeast_gradShift (τ : G.E → ℤ) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
          ∧ E = ω ⬝ᵥ ω}
      ((G.basisGramData B).energy (fun j => τ ⬝ᵥ G.cyclesZ B j)) := by
  have h := HarmonicGramData.ofCycles_energy_isLeast (V := G.V)
    (G.cyclesR B) (G.gramOf_cyclesR_posDef B)
    (fun j => τ ⬝ᵥ G.cyclesZ B j)
  have hset : {E : ℝ | ∃ ω : G.E → ℝ,
      (∀ j, ω ⬝ᵥ G.cyclesR B j
        = (((fun j => τ ⬝ᵥ G.cyclesZ B j) j : ℤ) : ℝ)) ∧ E = ω ⬝ᵥ ω}
      = {E : ℝ | ∃ ω : G.E → ℝ,
      (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
        ∧ E = ω ⬝ᵥ ω} := by
    ext E
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (G.periods_eq_cast_iff B τ ω).mp hω, rfl⟩
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (G.periods_eq_cast_iff B τ ω).mpr hω, rfl⟩
  rw [hset] at h
  exact h

/-- **The intrinsic harmonic energy** of an integer cohomology class:
defined through the fundamental basis; every basis computes it
(`energy_eq_harmonicEnergy`). -/
noncomputable def harmonicEnergy
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv κ)

/-- **The variational identity for every finite graph**: the class
energy is the least cochain energy among
realizers of the class's periods — attained. -/
theorem harmonicEnergy_isLeast
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv κ j : ℤ) : ℝ))
          ∧ E = ω ⬝ᵥ ω}
      (G.harmonicEnergy κ) :=
  HarmonicGramData.ofCycles_energy_isLeast (V := G.V) G.fundCyclesR
    (G.gramOf_cyclesR_posDef G.cycleBasis) (G.h1QuotEquiv κ)

/-- **Every basis computes the intrinsic energy**: the energy any
lattice basis assigns to the
periods of `τ` is the harmonic energy of `τ`'s class. -/
theorem energy_eq_harmonicEnergy (τ : G.E → ℤ) :
    (G.basisGramData B).energy (fun j => τ ⬝ᵥ G.cyclesZ B j)
      = G.harmonicEnergy (Submodule.Quotient.mk τ) := by
  have h1 := G.isLeast_gradShift B τ
  have h2 := G.isLeast_gradShift G.cycleBasis τ
  have hval := h1.unique h2
  rw [hval]
  show (G.basisGramData G.cycleBasis).energy
      (fun j => τ ⬝ᵥ G.cyclesZ G.cycleBasis j)
    = (G.basisGramData G.cycleBasis).energy
      (G.h1QuotEquiv (Submodule.Quotient.mk τ))
  rw [G.h1QuotEquiv_mk τ]
  rfl

/-- **The chart identity**: any basis's Gram energy at a class's
keystone coordinates is the intrinsic harmonic energy. -/
theorem basisGramData_energy_latticeQuot
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    (G.basisGramData B).energy (G.latticeQuotEquiv B κ)
      = G.harmonicEnergy κ := by
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [G.latticeQuotEquiv_mk B τ]
  exact G.energy_eq_harmonicEnergy B τ

/-- **Nonzero classes have positive energy** — intrinsic. -/
theorem harmonicEnergy_pos
    {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)} (hκ : κ ≠ 0) :
    0 < G.harmonicEnergy κ :=
  (G.basisGramData G.cycleBasis).energy_pos_of_ne_zero
    (G.h1QuotEquiv κ)
    (fun h0 => hκ (G.h1QuotEquiv.injective (h0.trans (map_zero _).symm)))

/-- The zero class has zero harmonic energy — the zero sector of the
intrinsic carrier (`classSectorAction`, below). -/
theorem harmonicEnergy_zero : G.harmonicEnergy 0 = 0 := by
  show (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv 0) = 0
  rw [map_zero]
  exact (G.basisGramData G.cycleBasis).energy_zero

end HarmonicEnergy

/-! ## The partition function of the graph -/

/-- **The partition function of the graph** — computed through the
fundamental basis; every basis's Boltzmann sum is the intrinsic class
sum (`basisGramData_partFn_eq_tsum_classes`). -/
noncomputable def partFn : ℝ :=
  (G.basisGramData G.cycleBasis).toQuadraticAction.toSectorAction.partFn

/-- Every lattice basis's Boltzmann sum is the intrinsic class sum:
reindex along the keystone equivalence and transport each term by the
chart identity. -/
theorem basisGramData_partFn_eq_tsum_classes {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          Real.exp (-(G.harmonicEnergy κ)) := by
  show ∑' k : Fin n → ℤ, Real.exp (-(G.basisGramData B).energy k) = _
  rw [← Equiv.tsum_eq (G.latticeQuotEquiv B).toEquiv
    (fun k => Real.exp (-(G.basisGramData B).energy k))]
  exact tsum_congr fun κ => by
    rw [show ((G.latticeQuotEquiv B).toEquiv κ : Fin n → ℤ)
        = G.latticeQuotEquiv B κ from rfl,
      G.basisGramData_energy_latticeQuot B κ]

/-! ## The intrinsic carrier

The carrier, as one object: the sector
lattice is `H¹(G;ℤ)` and the action is the harmonic energy — the
positive-definite quadratic action in intrinsic form, with the zero
class as the zero-energy sector. The keystone equivalence
`latticeQuotEquiv B` transports the energies, and the partition
function is the graph's (`classSectorAction_partFn`). -/

/-- **The intrinsic polarized form on `H¹(G;ℤ)`**: the
Gram bilinear form of the fundamental basis at the classes' keystone
coordinates. Basis-independent by `classForm_chart`. -/
noncomputable def classForm
    (κ κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  (G.basisGramData G.cycleBasis).interaction
    (G.h1QuotEquiv κ) (G.h1QuotEquiv κ')

/-- The quadratic law: the harmonic energy is the form's diagonal. -/
theorem classForm_self (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.classForm κ κ = G.harmonicEnergy κ := rfl

theorem classForm_comm (κ κ') : G.classForm κ κ' = G.classForm κ' κ := by
  unfold classForm HarmonicGramData.interaction
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (G.basisGramData G.cycleBasis).gram j i
      = (G.basisGramData G.cycleBasis).gram i j from by
    have h := (G.basisGramData G.cycleBasis).gram_symm
    calc (G.basisGramData G.cycleBasis).gram j i
        = (G.basisGramData G.cycleBasis).gramᵀ i j := rfl
      _ = (G.basisGramData G.cycleBasis).gram i j := by rw [h]]
  ring

theorem classForm_add_left (κ₁ κ₂ κ') :
    G.classForm (κ₁ + κ₂) κ' = G.classForm κ₁ κ' + G.classForm κ₂ κ' := by
  unfold classForm HarmonicGramData.interaction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add]
  push_cast [Pi.add_apply]
  ring

/-- **Basis charts preserve the form**: the Gram
interaction of any basis at the keystone coordinates is the intrinsic
polarized form — via polarization from the chart identity for
energies, with no coordinate transport. -/
theorem classForm_chart {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)
    (κ κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    (G.basisGramData B).interaction
        (G.latticeQuotEquiv B κ) (G.latticeQuotEquiv B κ')
      = G.classForm κ κ' := by
  have hpol : ∀ (H : HarmonicGramData G.V) (a b : Fin H.r → ℤ),
      H.interaction a b = (H.energy (a + b) - H.energy a - H.energy b) / 2 := by
    intro H a b
    have h := H.energy_add a b
    linarith
  show _ = (G.basisGramData G.cycleBasis).interaction
    (G.h1QuotEquiv κ) (G.h1QuotEquiv κ')
  rw [hpol, hpol]
  -- `rw [hpol]` instantiates the addends at `Fin H.r`, leaving the
  -- projection unreduced in the `Pi.instAdd` instance; the energy
  -- lemmas below live at `Fin n`. Restate so the two agree.
  show ((G.basisGramData B).energy
        (G.latticeQuotEquiv B κ + G.latticeQuotEquiv B κ')
      - (G.basisGramData B).energy (G.latticeQuotEquiv B κ)
      - (G.basisGramData B).energy (G.latticeQuotEquiv B κ')) / 2
    = ((G.basisGramData G.cycleBasis).energy
        (G.h1QuotEquiv κ + G.h1QuotEquiv κ')
      - (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv κ)
      - (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv κ')) / 2
  have h1 : (G.basisGramData B).energy
      (G.latticeQuotEquiv B κ + G.latticeQuotEquiv B κ')
      = (G.basisGramData G.cycleBasis).energy
        (G.h1QuotEquiv κ + G.h1QuotEquiv κ') := by
    rw [show G.latticeQuotEquiv B κ + G.latticeQuotEquiv B κ'
        = G.latticeQuotEquiv B (κ + κ') from (map_add _ κ κ').symm,
      show G.h1QuotEquiv κ + G.h1QuotEquiv κ'
        = G.h1QuotEquiv (κ + κ') from (map_add _ κ κ').symm,
      G.basisGramData_energy_latticeQuot B (κ + κ')]
    rfl
  have h2 := G.basisGramData_energy_latticeQuot B κ
  have h3 := G.basisGramData_energy_latticeQuot B κ'
  rw [h1, h2, h3]
  rfl

private lemma interaction_single {W : Type*} (H : HarmonicGramData W)
    (i j : Fin H.r) :
    H.interaction (Pi.single i 1) (Pi.single j 1) = H.gram i j := by
  show ∑ k, ∑ l, H.gram k l * ((Pi.single i 1 : Fin H.r → ℤ) k : ℝ)
      * ((Pi.single j 1 : Fin H.r → ℤ) l : ℝ) = H.gram i j
  rw [Finset.sum_eq_single i
    (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j
    (fun l _ hl => by simp [Pi.single_eq_of_ne hl])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- The Gram entries of the intrinsic form at the induced `H¹` basis
are the basis's Gram data — `classForm_chart` at the standard basis
vectors. -/
theorem classForm_h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (i j : Fin n) :
    G.classForm (G.h1Basis B i) (G.h1Basis B j)
      = (G.basisGramData B).gram i j := by
  rw [← G.classForm_chart B, latticeQuotEquiv_h1Basis, latticeQuotEquiv_h1Basis]
  exact interaction_single (G.basisGramData B) i j

/-- **THE INTRINSIC QUADRATIC-LATTICE ACTION**: the
carrier as one bundled object — the lattice `H¹(G;ℤ)` with
the polarized form `classForm`, positive definite on the **real scalar
extension**: the field is discharged from the Gram chart
of the fundamental basis (`bilinBaseChange_posDef_of_gram`), and
integral positivity and summability are theorems of the bundle. Every
basis chart preserves the form (`classForm_chart`). -/
noncomputable def classQuadAction : QuadLatticeAction.{v} where
  Λ := (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)
  form := G.classForm
  form_comm := G.classForm_comm
  form_add_left := G.classForm_add_left
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _ (G.h1Basis G.cycleBasis) ?_
    have hmat : (Matrix.of fun i j =>
          G.classForm (G.h1Basis G.cycleBasis i) (G.h1Basis G.cycleBasis j))
        = (G.basisGramData G.cycleBasis).gram := by
      ext i j
      rw [Matrix.of_apply]
      exact G.classForm_h1Basis G.cycleBasis i j
    rw [hmat]
    exact (G.basisGramData G.cycleBasis).gram_posDef

/-- **THE INTRINSIC CARRIER**: the analytic
projection of the intrinsic quadratic-lattice action —
the sector lattice `H¹(G;ℤ)` with the harmonic energy
`E κ = classForm κ κ`, as a `SectorAction`. -/
noncomputable def classSectorAction : SectorAction.{v} :=
  (G.classQuadAction).toSectorAction

/-- The intrinsic carrier's partition function is the graph's. -/
theorem classSectorAction_partFn :
    (G.classSectorAction).partFn = G.partFn := by
  show (∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
      Real.exp (-G.harmonicEnergy κ)) = G.partFn
  rw [← G.basisGramData_partFn_eq_tsum_classes G.cycleBasis]
  rfl

/-! ### The inverse-temperature scaling of the intrinsic carrier

The scaled carrier (`classQuadActionβ` — `β·classForm`, positive
definite for `β > 0`), its sector action (`classSectorActionβ`), and
the carrier's β-scaled partition function (`classScaledPartFn`), with
positivity and the cumulant reading
(`log_classScaledPartFn_eq_cgf`). -/

/-- **The inverse-temperature scaling of the intrinsic carrier**: a
**direct specialization** of the bundle
operation `QuadLatticeAction.scale`. -/
noncomputable def classQuadActionβ (β : ℝ) (hβ : 0 < β) :
    QuadLatticeAction.{v} :=
  (G.classQuadAction).scale β hβ

/-- The β-scaled carrier as a sector action: `E = β·harmonicEnergy`. -/
noncomputable def classSectorActionβ (β : ℝ) (hβ : 0 < β) :
    SectorAction.{v} :=
  (G.classQuadActionβ β hβ).toSectorAction

/-- The carrier's β-scaled partition function — the bundle's,
specialized. -/
noncomputable def classScaledPartFn (β : ℝ) : ℝ :=
  (G.classQuadAction).scaledPartFn β

/-- The β-scaled carrier partition function is positive at `0 < β` —
the scaled bundle's sector action computes it. -/
theorem classScaledPartFn_pos (β : ℝ) (hβ : 0 < β) :
    0 < G.classScaledPartFn β :=
  (G.classSectorActionβ β hβ).partFn_pos

/-- **The temperature recognition**: the log β-scaled partition
function is the harmonic complexity plus the cumulant functional of
the temperature-shift observable — the identity
`⟨e^{(1−β)E}⟩ = Z(β)/Z` on the intrinsic carrier; summability is
the standing scaled bundle's (`classSectorActionβ`). -/
theorem log_classScaledPartFn_eq_cgf (β : ℝ) (hβ : 0 < β) :
    Real.log (G.classScaledPartFn β)
      = (G.classSectorAction).complexity
        + (G.classSectorAction).cgf
            (fun κ => (1 - β) * G.harmonicEnergy κ) := by
  have hZ := (G.classSectorAction).partFn_pos
  have hZβ := G.classScaledPartFn_pos β hβ
  have hterm : ∀ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
      Real.exp ((1 - β) * G.harmonicEnergy κ)
        * (G.classSectorAction).gibbsMass κ
      = Real.exp (-(β * G.harmonicEnergy κ))
        * ((G.classSectorAction).partFn)⁻¹ := by
    intro κ
    show Real.exp ((1 - β) * G.harmonicEnergy κ)
        * (Real.exp (-G.harmonicEnergy κ)
            / (G.classSectorAction).partFn) = _
    rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add,
      show (1 - β) * G.harmonicEnergy κ + -G.harmonicEnergy κ
        = -(β * G.harmonicEnergy κ) from by ring]
  have hexp : (G.classSectorAction).gibbsExpect
      (fun κ => Real.exp ((1 - β) * G.harmonicEnergy κ))
      = G.classScaledPartFn β / (G.classSectorAction).partFn := by
    show (∑' κ, Real.exp ((1 - β) * G.harmonicEnergy κ)
        * (G.classSectorAction).gibbsMass κ) = _
    rw [tsum_congr hterm, tsum_mul_right, ← div_eq_mul_inv]
    rfl
  show Real.log (G.classScaledPartFn β)
    = Real.log (G.classSectorAction).partFn
      + Real.log ((G.classSectorAction).gibbsExpect
          fun κ => Real.exp ((1 - β) * G.harmonicEnergy κ))
  rw [hexp, Real.log_div hZβ.ne' hZ.ne']
  ring

end IncidenceGraph

end Theaetetus
