import Theaetetus.Tower
import Theaetetus.Pullback
import Theaetetus.GraphInstances
import Theaetetus.Witness

/-! # The defect on the tower, and the cross-ratio law

The central object of the program at carrier level: for a finite
multigraph `G` and resolutions `q, q′`, **the defect**

    D_G(q, q′) := [K(lcm) + K(gcd)] − [K(q) + K(q′)]

where `K(q)` is the complexity of the residue action on
`H¹(G;ℤ) ⧸ q·H¹`. The seed theorems, at home:

* **The key lemma** (`residueWeight_zero_eq_classScaledPartFn`):
  the modal coset weight at resolution `q` is the `q²`-scaled
  partition function — squares of resolutions are forced by the
  quadratic energy, not chosen.
* **The cross-ratio law** (`crossRatio_law`): the defect is a
  cross-ratio of scaled partition functions; its cumulant form
  (`crossRatio_law_cgf`) is the analytic handle.
* **The boundary** (`towerDefect_eq_zero_of_dvd`): the defect
  vanishes on chains.
* **The coupling reading** (`h1ReductionCRT`): the `lcm`-resolution
  is the fiber product of the two resolutions over their common
  coarsening — `D` is the defect of a genuine coupling.
* **The carrier bridge** (`cycle3_towerDefect_eq_defect`): on
  `cycleGraph 3` the carrier defect *is* the rank-one defect at
  scale `1/3` — so the strictness witness
  (`cycle3_towerDefect_neg`) is a corollary of the rank-one
  program (M2/M3), not a re-derivation. -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u v

/-! ## `gcd`/`lcm` positivity instances -/

instance (q q' : ℕ) [NeZero q] : NeZero (Nat.gcd q q') :=
  ⟨fun h0 => NeZero.ne q (Nat.eq_zero_of_gcd_eq_zero_left h0)⟩

instance (q q' : ℕ) [NeZero q] [NeZero q'] : NeZero (Nat.lcm q q') := by
  constructor
  intro h0
  have h := Nat.gcd_mul_lcm q q'
  rw [h0, mul_zero] at h
  exact absurd h.symm (mul_ne_zero (NeZero.ne q) (NeZero.ne q'))

/-! ## Quadratic scaling of the harmonic energy -/

/-- The Gram-form energy scales quadratically under integer scalar
multiplication of the sector. -/
theorem HarmonicGramData.energy_zsmul {V : Type u} (H : HarmonicGramData V)
    (c : ℤ) (k : Fin H.r → ℤ) :
    H.energy (c • k) = ((c : ℝ)) ^ 2 * H.energy k := by
  show ∑ i, ∑ j, H.gram i j * ((c • k) i : ℝ) * ((c • k) j : ℝ)
    = (c : ℝ) ^ 2 * ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show H.gram i j * ((c * k i : ℤ) : ℝ) * ((c * k j : ℤ) : ℝ)
    = (c : ℝ) ^ 2 * (H.gram i j * (k i : ℝ) * (k j : ℝ))
  push_cast
  ring

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-- **The harmonic energy is quadratic**:
`E(c • κ) = c² · E(κ)`. -/
theorem harmonicEnergy_zsmul (c : ℤ)
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.harmonicEnergy (c • κ) = ((c : ℝ)) ^ 2 * G.harmonicEnergy κ := by
  show (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv (c • κ)) = _
  rw [map_smul]
  exact HarmonicGramData.energy_zsmul _ c _

/-! ## The key lemma -/

/-- **THE KEY LEMMA**: the modal coset weight is the scaled
partition function — `residueWeight q 0 = classScaledPartFn (q²)`.
The fiber of zero is `q·H¹`, multiplication by `q` enumerates it
from the carrier (injectively, on the free lattice), and the energy
is quadratic. -/
theorem residueWeight_zero_eq_classScaledPartFn (q : ℕ) [NeZero q] :
    G.residueWeight q 0 = G.classScaledPartFn ((q : ℝ) ^ 2) := by
  have hq0 : ((q : ℤ)) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hbij : Function.Bijective
      (fun κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
        (⟨(q : ℤ) • κ', by
          rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨κ', rfl⟩⟩ :
        {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
          (Submodule.Quotient.mk κ : H1Reduction G q) = 0})) := by
    constructor
    · intro a b hab
      have h := Subtype.ext_iff.mp hab
      have h2 := congrArg (⇑G.h1QuotEquiv) h
      rw [map_smul, map_smul] at h2
      apply G.h1QuotEquiv.injective
      funext i
      have h3 := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul] at h3
      exact mul_left_cancel₀ hq0 h3
    · rintro ⟨κ, hκ⟩
      rw [Submodule.Quotient.mk_eq_zero] at hκ
      obtain ⟨κ', hκ'⟩ := hκ
      exact ⟨κ', Subtype.ext (by
        show (q : ℤ) • κ' = κ
        simpa using hκ')⟩
  show (∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = 0},
    (G.classSectorAction).weight κ.val) = _
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)
    (fun κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
        (Submodule.Quotient.mk κ : H1Reduction G q) = 0} =>
      (G.classSectorAction).weight κ.val)]
  refine tsum_congr fun κ' => ?_
  show Real.exp (-(G.harmonicEnergy ((q : ℤ) • κ')))
    = Real.exp (-((q : ℝ) ^ 2 * G.harmonicEnergy κ'))
  rw [G.harmonicEnergy_zsmul (q : ℤ) κ']
  push_cast
  ring_nf

/-- The residue complexity in scaled-partition-function form: the
harmonic complexity minus the log modal weight. -/
theorem residueAction_complexity_eq (q : ℕ) [NeZero q] :
    (G.residueAction q).complexity
      = (G.classSectorAction).complexity
        - Real.log (G.classScaledPartFn ((q : ℝ) ^ 2)) := by
  have h := G.classComplexity_residue_split q
  rw [G.residueWeight_zero_eq_classScaledPartFn q] at h
  linarith

/-! ## The defect and the exact law -/

/-- **THE DEFECT** on the tower: the four-term inclusion–exclusion
of residue complexities over the interval `[gcd, lcm]` of the
divisibility lattice. The central object of the program, at carrier
level. -/
noncomputable def towerDefect (q q' : ℕ) [NeZero q] [NeZero q'] : ℝ :=
  ((G.residueAction (Nat.lcm q q')).complexity
      + (G.residueAction (Nat.gcd q q')).complexity)
    - ((G.residueAction q).complexity + (G.residueAction q').complexity)

/-- **THE CROSS-RATIO LAW** (the exact law): the defect is a
cross-ratio of scaled partition functions — each residue complexity
is the harmonic complexity minus a scaled log, and the base
complexities cancel in the four-term combination. -/
theorem crossRatio_law (q q' : ℕ) [NeZero q] [NeZero q'] :
    G.towerDefect q q'
    = (Real.log (G.classScaledPartFn ((q : ℝ) ^ 2))
        + Real.log (G.classScaledPartFn ((q' : ℝ) ^ 2)))
      - (Real.log (G.classScaledPartFn ((Nat.gcd q q' : ℝ) ^ 2))
        + Real.log (G.classScaledPartFn ((Nat.lcm q q' : ℝ) ^ 2))) := by
  unfold towerDefect
  rw [G.residueAction_complexity_eq q, G.residueAction_complexity_eq q',
    G.residueAction_complexity_eq (Nat.gcd q q'),
    G.residueAction_complexity_eq (Nat.lcm q q')]
  ring

/-- **The cumulant form**: substituting the temperature recognition
(`log_classScaledPartFn_eq_cgf`) into the cross-ratio law, the four
class complexities cancel — the defect is the four-term cumulant
combination of energy observables on the intrinsic carrier. -/
theorem crossRatio_law_cgf (q q' : ℕ) [NeZero q] [NeZero q'] :
    G.towerDefect q q'
    = ((G.classSectorAction).cgf
          (fun κ => (1 - ((q : ℝ)) ^ 2) * G.harmonicEnergy κ)
        + (G.classSectorAction).cgf
          (fun κ => (1 - ((q' : ℝ)) ^ 2) * G.harmonicEnergy κ))
      - ((G.classSectorAction).cgf
          (fun κ => (1 - ((Nat.gcd q q' : ℝ)) ^ 2) * G.harmonicEnergy κ)
        + (G.classSectorAction).cgf
          (fun κ => (1 - ((Nat.lcm q q' : ℝ)) ^ 2) * G.harmonicEnergy κ)) := by
  have hpos : ∀ (m : ℕ) [NeZero m], (0 : ℝ) < (m : ℝ) ^ 2 := fun m _ =>
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)) 2
  rw [G.crossRatio_law q q',
    G.log_classScaledPartFn_eq_cgf ((q : ℝ) ^ 2) (hpos q),
    G.log_classScaledPartFn_eq_cgf ((q' : ℝ) ^ 2) (hpos q'),
    G.log_classScaledPartFn_eq_cgf ((Nat.gcd q q' : ℝ) ^ 2)
      (hpos (Nat.gcd q q')),
    G.log_classScaledPartFn_eq_cgf ((Nat.lcm q q' : ℝ) ^ 2)
      (hpos (Nat.lcm q q'))]
  ring

/-- **The boundary**: the defect vanishes on chains — along `q ∣ q′`
the pair `{gcd, lcm}` collapses to `{q, q′}` and the cross-ratio
cancels identically. -/
theorem towerDefect_eq_zero_of_dvd (q q' : ℕ) [NeZero q] [NeZero q']
    (hdvd : q ∣ q') :
    G.towerDefect q q' = 0 := by
  rw [G.crossRatio_law q q', Nat.gcd_eq_left hdvd,
    Nat.dvd_antisymm (Nat.lcm_dvd hdvd dvd_rfl) (Nat.dvd_lcm_right q q')]
  ring

/-! ## Chinese remainder on the tower -/

/-- **CRT ON THE TOWER**: the `lcm` reduction is the fiber
product of the two reductions over their common coarsening — the
finer resolution **is** the coupling of the coarser ones, so the
cross-ratio law is the defect of a genuine coupling.
Componentwise Chinese remainder: injectivity is `lcm`-divisibility
of the keystone coordinates, surjectivity is the fiber count. -/
noncomputable def h1ReductionCRT (q q' : ℕ) [NeZero q] [NeZero q'] :
    H1Reduction G (Nat.lcm q q')
      ≃ Pullback
          (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
          (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q'))) := by
  haveI : Finite (Pullback
      (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
      (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q')))) :=
    inferInstanceAs (Finite
      {p : H1Reduction G q × H1Reduction G q' //
        G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q') p.1
          = G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q') p.2})
  refine Equiv.ofBijective
    (fun ξ => ⟨(G.h1TowerMap q (Nat.lcm q q') (Nat.dvd_lcm_left q q') ξ,
        G.h1TowerMap q' (Nat.lcm q q') (Nat.dvd_lcm_right q q') ξ), ?_⟩)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rfl
  · intro ξ η hξη
    obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    obtain ⟨κ', rfl⟩ := Submodule.Quotient.mk_surjective _ η
    have hpair := Subtype.ext_iff.mp hξη
    have h1 : (Submodule.Quotient.mk κ : H1Reduction G q)
        = Submodule.Quotient.mk κ' := congrArg Prod.fst hpair
    have h2 : (Submodule.Quotient.mk κ : H1Reduction G q')
        = Submodule.Quotient.mk κ' := congrArg Prod.snd hpair
    rw [Submodule.Quotient.eq] at h1 h2 ⊢
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have ha' : (q : ℤ) • a = κ - κ' := ha
    have hb' : (q' : ℤ) • b = κ - κ' := hb
    have hdvd : ∀ i, ((Nat.lcm q q' : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
      intro i
      have hqa : ((q : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
        refine ⟨G.h1QuotEquiv a i, ?_⟩
        have h := congrFun (congrArg (⇑G.h1QuotEquiv) ha') i
        rw [map_smul] at h
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      have hqb : ((q' : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
        refine ⟨G.h1QuotEquiv b i, ?_⟩
        have h := congrFun (congrArg (⇑G.h1QuotEquiv) hb') i
        rw [map_smul] at h
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      rw [← Int.natAbs_dvd_natAbs] at hqa hqb ⊢
      rw [Int.natAbs_natCast] at hqa hqb ⊢
      exact Nat.lcm_dvd hqa hqb
    choose y hy using hdvd
    refine ⟨(G.h1QuotEquiv).symm y, ?_⟩
    show ((Nat.lcm q q' : ℕ) : ℤ) • ((G.h1QuotEquiv).symm y) = κ - κ'
    apply G.h1QuotEquiv.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext i
    show ((Nat.lcm q q' : ℕ) : ℤ) * y i = G.h1QuotEquiv (κ - κ') i
    exact (hy i).symm
  · have hq : q = q / Nat.gcd q q' * Nat.gcd q q' :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left q q')).symm
    have hq' : q' = q' / Nat.gcd q q' * Nat.gcd q q' :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_right q q')).symm
    have hfib : ∀ d : H1Reduction G (Nat.gcd q q'),
        Nat.card (FiberProd
          (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
          (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q'))) d)
          = (q / Nat.gcd q q') ^ G.b1 * (q' / Nat.gcd q q') ^ G.b1 := by
      intro d
      rw [Nat.card_prod,
        G.card_h1TowerMap_fiber (Nat.gcd q q') q (q / Nat.gcd q q')
          (Nat.gcd_dvd_left q q') hq d,
        G.card_h1TowerMap_fiber (Nat.gcd q q') q' (q' / Nat.gcd q q')
          (Nat.gcd_dvd_right q q') hq' d]
    have harith : Nat.lcm q q'
        = Nat.gcd q q' * (q / Nat.gcd q q') * (q' / Nat.gcd q q') := by
      have hgcd0 : 0 < Nat.gcd q q' :=
        Nat.pos_of_ne_zero (NeZero.ne (Nat.gcd q q'))
      apply Nat.eq_of_mul_eq_mul_left hgcd0
      calc Nat.gcd q q' * Nat.lcm q q' = q * q' := Nat.gcd_mul_lcm q q'
        _ = (Nat.gcd q q' * (q / Nat.gcd q q'))
            * (Nat.gcd q q' * (q' / Nat.gcd q q')) := by
            rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left q q'),
              Nat.mul_div_cancel' (Nat.gcd_dvd_right q q')]
        _ = Nat.gcd q q'
            * (Nat.gcd q q' * (q / Nat.gcd q q') * (q' / Nat.gcd q q')) := by
            ring
    rw [G.card_H1Reduction (Nat.lcm q q'),
      Nat.card_congr (Pullback.equivSigmaFiber _ _), Nat.card_sigma,
      Finset.sum_congr rfl fun d _ => hfib d, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card,
      G.card_H1Reduction (Nat.gcd q q'), smul_eq_mul, harith]
    ring

/-- **Counting on the tower**: the CRT counting identity —
`Nat.gcd_mul_lcm` raised to `b₁`. -/
theorem card_h1Reduction_mul_gcd (q q' : ℕ) [NeZero q] [NeZero q'] :
    Nat.card (H1Reduction G (Nat.lcm q q'))
        * Nat.card (H1Reduction G (Nat.gcd q q'))
      = Nat.card (H1Reduction G q) * Nat.card (H1Reduction G q') := by
  rw [G.card_H1Reduction (Nat.lcm q q'), G.card_H1Reduction (Nat.gcd q q'),
    G.card_H1Reduction q, G.card_H1Reduction q', ← mul_pow, ← mul_pow,
    show Nat.lcm q q' * Nat.gcd q q' = q * q' from by
      rw [mul_comm]
      exact Nat.gcd_mul_lcm q q']

end IncidenceGraph

/-! ## The carrier bridge: `C₃` reduces to the rank-one program -/

/-- **The `C₃` scaled partition functions are the theta values**:
the rank-one carrier with energy `k²/3` sums to `θ(s/3)`. -/
theorem cycle3_classScaledPartFn (s : ℝ) :
    (cycleGraph 3 (by norm_num)).classScaledPartFn s = theta (s / 3) := by
  have hE : ∀ k : ℤ,
      (cycleGraph 3 (by norm_num)).harmonicEnergy
          (((cycleGraph 3 (by norm_num)).latticeQuotEquiv
              (cycleLatticeBasis 3 (by norm_num))).symm
            ((Equiv.funUnique (Fin 1) ℤ).symm k))
        = (k : ℝ) ^ 2 / 3 := by
    intro k
    rw [← (cycleGraph 3 (by norm_num)).basisGramData_energy_latticeQuot
      (cycleLatticeBasis 3 (by norm_num)), LinearEquiv.apply_symm_apply]
    show ∑ i, ∑ j,
        (gramOf ((cycleGraph 3 (by norm_num)).cyclesR
            (cycleLatticeBasis 3 (by norm_num))))⁻¹ i j
          * (((Equiv.funUnique (Fin 1) ℤ).symm k) i : ℝ)
          * (((Equiv.funUnique (Fin 1) ℤ).symm k) j : ℝ)
      = (k : ℝ) ^ 2 / 3
    rw [cyclesR_cycleLatticeBasis 3 (by norm_num), gramOf_cycleAllOnes,
      inv_fin_one ((3 : ℕ) : ℝ) (by norm_num)]
    norm_num [Fin.sum_univ_one, Equiv.funUnique_symm_apply]
    ring
  show (∑' κ : (Fin 3 → ℤ) ⧸ LinearMap.range
      ((cycleGraph 3 (by norm_num)).gradLin ℤ),
    Real.exp (-(s
      * (cycleGraph 3 (by norm_num)).harmonicEnergy κ))) = _
  rw [← Equiv.tsum_eq
    ((Equiv.funUnique (Fin 1) ℤ).symm.trans
      ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
        (cycleLatticeBasis 3 (by norm_num))).symm.toEquiv)
    (fun κ => Real.exp (-(s
      * (cycleGraph 3 (by norm_num)).harmonicEnergy κ)))]
  refine tsum_congr fun k => ?_
  rw [show ((Equiv.funUnique (Fin 1) ℤ).symm.trans
      ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
        (cycleLatticeBasis 3 (by norm_num))).symm.toEquiv) k
      = ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
          (cycleLatticeBasis 3 (by norm_num))).symm
        ((Equiv.funUnique (Fin 1) ℤ).symm k) from rfl,
    hE k]
  congr 1
  ring

/-- **THE CARRIER BRIDGE**: on `cycleGraph 3` the carrier defect at
any pair of resolutions *is* the rank-one defect at scale `1/3`.
The tower face of the seed reduces to the rank-one program. -/
theorem cycle3_towerDefect_eq_defect (q q' : ℕ) [NeZero q] [NeZero q'] :
    (cycleGraph 3 (by norm_num)).towerDefect q q' = defect (1 / 3) q q' := by
  rw [(cycleGraph 3 (by norm_num)).crossRatio_law q q',
    cycle3_classScaledPartFn, cycle3_classScaledPartFn,
    cycle3_classScaledPartFn, cycle3_classScaledPartFn,
    show ((q : ℝ)) ^ 2 / 3 = (q : ℝ) ^ 2 * (1 / 3) from by ring,
    show ((q' : ℝ)) ^ 2 / 3 = (q' : ℝ) ^ 2 * (1 / 3) from by ring,
    show ((Nat.gcd q q' : ℝ)) ^ 2 / 3
      = (Nat.gcd q q' : ℝ) ^ 2 * (1 / 3) from by ring,
    show ((Nat.lcm q q' : ℝ)) ^ 2 / 3
      = (Nat.lcm q q' : ℝ) ^ 2 * (1 / 3) from by ring]
  rfl

/-- **The strictness, at home**: the carrier defect on `C₃` at the
incomparable pair `(2, 3)` is strictly negative — now a corollary
of the rank-one witness (M2), itself a point of the all-scales
theorem (M3). At the witness, incomparable resolutions couple
supermodularly. -/
theorem cycle3_towerDefect_neg :
    (cycleGraph 3 (by norm_num)).towerDefect 2 3 < 0 := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_witness

end Theaetetus
