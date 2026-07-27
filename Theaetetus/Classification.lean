import Theaetetus.CrossRatio
import Theaetetus.Submodular
import Theaetetus.PartitionTower

/-! # The classification: Euler-factorizable towers

**The zero-defect classification.** Call a tower
**Euler-factorizable** when its defect matrix
vanishes identically — equivalently, when its complexity is a
valuation on the divisibility lattice, the algebraic shadow of an
Euler product. This module settles the question at every level the
program formalizes, by instantiating the abstract classification of
`PartitionTower.lean`:

* **every positive-definite lattice action** is a partition tower
  (`QuadLatticeAction.toPartitionTower`), so its intrinsic defect
  vanishes identically iff the lattice is trivial
  (`QuadLatticeAction.defect_forall_eq_zero_iff`);
* **every graph carrier** instantiates through its intrinsic bundle,
  and the cross-ratio law identifies its residue-complexity defect
  with the tower's (`towerDefect_eq_partitionTower_defect`) — the
  carrier classification (`towerDefect_forall_eq_zero_iff`) and the
  asymptotic sign (`eventually_towerDefect_neg`) follow;
* on **`C₃`** the per-pair kernel is computed exactly through the
  carrier bridge and Q1 at rank one: the kernel is the chain
  relation (`cycle3_towerDefect_eq_zero_iff`). -/

namespace Theaetetus

/-- **The sign on `C₃`, everywhere** (Q1 at the first carrier,
closed): the tower defect of the smallest rank-one carrier is
strictly negative at every incomparable pair of resolutions. -/
theorem cycle3_towerDefect_neg_of_incomparable (q q' : ℕ) [NeZero q] [NeZero q']
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    (cycleGraph 3 (by norm_num)).towerDefect q q' < 0 := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_neg_of_incomparable (by norm_num) hqq' hq'q

/-- **The kernel on `C₃`** (the classification at the first
carrier): the tower
defect vanishes exactly on chains — `C₃` is not Euler-factorizable,
and its defect matrix detects divisibility. -/
theorem cycle3_towerDefect_eq_zero_iff (q q' : ℕ) [NeZero q] [NeZero q'] :
    (cycleGraph 3 (by norm_num)).towerDefect q q' = 0 ↔ q ∣ q' ∨ q' ∣ q := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_eq_zero_iff (by norm_num)

/-! ## Every lattice action is a partition tower

The abstract classification instantiates at the full generality of
the bundled lattice actions: sectors are the lattice points, energy
the quadratic form, the modal sector the origin — positivity off the
origin is the bundle's integral positivity, summability is the
bundle's. **The zero-defect classification holds for every
positive-definite lattice**: the
intrinsic tower defect vanishes identically iff the lattice is
trivial. What a graph carrier adds on top is the residue-complexity
reading: its cross-ratio law *derives* this defect from the
complexities of honest residue actions, rather than defining it. -/

universe u

namespace QuadLatticeAction

variable (Q : QuadLatticeAction.{u})

/-- **Every positive-definite lattice action is a partition tower**:
sectors the lattice points, energy the form, modal sector the
origin. -/
noncomputable def toPartitionTower : PartitionTower.{u} where
  toSectorAction := Q.toSectorAction
  modal := (0 : Q.Λ)
  E_modal := Q.form_zero_left 0
  E_pos := fun a ha => Q.form_posDef a ha

/-- **THE ZERO-DEFECT CLASSIFICATION, EVERY POSITIVE-DEFINITE
LATTICE**: the intrinsic tower
defect vanishes at every pair of resolutions iff the lattice is
trivial. -/
theorem defect_forall_eq_zero_iff :
    (∀ q q' : ℕ, q ≠ 0 → q' ≠ 0 → Q.toPartitionTower.defect q q' = 0)
      ↔ Subsingleton Q.Λ := by
  rw [Q.toPartitionTower.defect_forall_eq_zero_iff]
  exact ⟨fun h => ⟨fun a b => (h a).trans (h b).symm⟩,
    fun h κ => @Subsingleton.elim _ h κ _⟩

end QuadLatticeAction

/-! ## The classification for every carrier — by instantiation

The carrier's classification is no longer proved directly: the
intrinsic bundle is a partition tower, the cross-ratio law reads the
residue-complexity defect as the tower's defect, and the abstract
theorems descend. Only the strict base excess keeps a carrier-level
proof, because the carrier can say more (`β > 0`, not just
`β ≥ 1`, through the scaled bundle's summability). -/

namespace IncidenceGraph

open Filter Topology

variable (G : IncidenceGraph.{u})

/-- **The carrier as a partition tower** — the lattice-action
instance, specialized to the intrinsic bundle. -/
noncomputable def toPartitionTower : PartitionTower.{u} :=
  G.classQuadAction.toPartitionTower

/-- The tower's scaled partition function is the carrier's. -/
theorem toPartitionTower_Z (β : ℝ) :
    G.toPartitionTower.Z β = G.classScaledPartFn β := rfl

/-- **The cross-ratio law, read as instantiation**: the carrier's
residue-complexity defect is its partition tower's defect. -/
theorem towerDefect_eq_partitionTower_defect (q q' : ℕ)
    [NeZero q] [NeZero q'] :
    G.towerDefect q q' = G.toPartitionTower.defect q q' := by
  rw [G.crossRatio_law q q']
  rfl

/-- **Saturation**: at infinite inverse temperature only the modal
class survives — the abstract theorem, instantiated. -/
theorem tendsto_classScaledPartFn_atTop :
    Tendsto G.classScaledPartFn atTop (𝓝 1) :=
  G.toPartitionTower.tendsto_Z_atTop

/-- The β-scaled class partition function, in Boltzmann-sum form. -/
private lemma classScaledPartFn_eq_tsum (β : ℝ) :
    G.classScaledPartFn β
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          Real.exp (-(β * G.harmonicEnergy κ)) := rfl

/-- **The base complexity is positive on a carrier with a cycle**: a
nonzero class contributes strictly to the Boltzmann sum at any
inverse temperature — stronger than the abstract `β ≥ 1` bound,
through the scaled bundle's summability. -/
theorem one_lt_classScaledPartFn {β : ℝ} (hβ : 0 < β)
    (hnt : ∃ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ), κ ≠ 0) :
    1 < G.classScaledPartFn β := by
  classical
  obtain ⟨κ₀, hκ₀⟩ := hnt
  rw [classScaledPartFn_eq_tsum]
  have hf : Summable (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      if κ = 0 then (1 : ℝ) else 0) :=
    ⟨1, hasSum_ite_eq 0 (1 : ℝ)⟩
  have hg : Summable (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      Real.exp (-(β * G.harmonicEnergy κ))) :=
    (G.classQuadAction.scale β hβ).summable
  have hle : ∀ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
      (if κ = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(β * G.harmonicEnergy κ)) := by
    intro κ
    by_cases hκ : κ = 0
    · subst hκ
      simp [G.harmonicEnergy_zero]
    · simp only [if_neg hκ]
      exact (Real.exp_pos _).le
  have hstrict : (if κ₀ = 0 then (1 : ℝ) else 0)
      < Real.exp (-(β * G.harmonicEnergy κ₀)) := by
    rw [if_neg hκ₀]
    exact Real.exp_pos _
  calc (1 : ℝ)
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          (if κ = 0 then (1 : ℝ) else 0) :=
        (tsum_ite_eq 0 (fun _ => (1 : ℝ))).symm
    _ < ∑' κ, Real.exp (-(β * G.harmonicEnergy κ)) :=
        hf.tsum_lt_tsum hle hstrict hg

/-- A carrier with trivial cycle lattice has trivial Boltzmann sums —
the abstract collapse, instantiated. -/
theorem classScaledPartFn_eq_one_of_subsingleton
    [hsub : Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))] (β : ℝ) :
    G.classScaledPartFn β = 1 :=
  G.toPartitionTower.Z_eq_one_of_forall_eq
    (fun κ => @Subsingleton.elim _ hsub κ _) β

/-- **The saturation limit of the defect**: along the staircase of
coprime pairs `(n+1, n+2)` the tower defect converges to minus the
base complexity `−log Z(1)` — the abstract staircase limit, read
through the cross-ratio bridge. -/
theorem tendsto_towerDefect_succ :
    Tendsto (fun n : ℕ => G.towerDefect (n + 1) (n + 2)) atTop
      (𝓝 (-Real.log (G.classScaledPartFn 1))) := by
  have h := G.toPartitionTower.tendsto_defect_succ
  have heq : ∀ n : ℕ, G.toPartitionTower.defect (n + 1) (n + 2)
      = G.towerDefect (n + 1) (n + 2) := fun n =>
    (G.towerDefect_eq_partitionTower_defect (n + 1) (n + 2)).symm
  simpa only [heq, G.toPartitionTower_Z] using h

/-- **The sign appears asymptotically in every rank**: on a carrier
with a cycle, the tower defect is eventually strictly negative along
the staircase — Q1's sign, at the saturation end, for every carrier. -/
theorem eventually_towerDefect_neg
    (hnt : ∃ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ), κ ≠ 0) :
    ∀ᶠ n : ℕ in atTop, G.towerDefect (n + 1) (n + 2) < 0 := by
  obtain ⟨κ₀, hκ₀⟩ := hnt
  filter_upwards [G.toPartitionTower.eventually_defect_neg ⟨κ₀, hκ₀⟩] with n hn
  rwa [G.towerDefect_eq_partitionTower_defect]

/-- **THE ZERO-DEFECT CLASSIFICATION, EVERY CARRIER**: the
defect matrix of a
carrier vanishes identically iff its cycle lattice is trivial — the
Euler-factorizable carriers are exactly those with `b₁ = 0`. The
abstract classification, read through the cross-ratio bridge. -/
theorem towerDefect_forall_eq_zero_iff :
    (∀ (q q' : ℕ) [NeZero q] [NeZero q'], G.towerDefect q q' = 0)
      ↔ Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) := by
  constructor
  · intro h
    have habs : ∀ q q' : ℕ, q ≠ 0 → q' ≠ 0 →
        G.toPartitionTower.defect q q' = 0 := by
      intro q q' hq hq'
      haveI : NeZero q := ⟨hq⟩
      haveI : NeZero q' := ⟨hq'⟩
      rw [← G.towerDefect_eq_partitionTower_defect]
      exact h q q'
    have htriv := (G.toPartitionTower.defect_forall_eq_zero_iff).mp habs
    exact ⟨fun a b => (htriv a).trans (htriv b).symm⟩
  · intro hsub q q' _ _
    rw [G.towerDefect_eq_partitionTower_defect]
    exact (G.toPartitionTower.defect_forall_eq_zero_iff).mpr
      (fun κ => @Subsingleton.elim _ hsub κ _) q q' (NeZero.ne q) (NeZero.ne q')

end IncidenceGraph

end Theaetetus
