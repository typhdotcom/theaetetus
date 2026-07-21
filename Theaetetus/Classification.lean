import Theaetetus.CrossRatio
import Theaetetus.Submodular
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Toward the classification: the kernel on the first carrier

**Q3, first slice.** Call a carrier **Euler-factorizable** when its
defect matrix vanishes identically — equivalently, when its residue
complexity is a valuation on the divisibility lattice, the algebraic
shadow of an Euler product. Q3 conjectures only rank zero qualifies.

On the first nontrivial carrier the question is now settled
completely: through the carrier bridge
(`cycle3_towerDefect_eq_defect`) and Q1 at rank one
(`defect_neg_of_incomparable`, `defect_eq_zero_iff`), the tower
defect of `C₃` is strictly negative at **every** incomparable pair
(`cycle3_towerDefect_neg_of_incomparable`), and its kernel is
**exactly** the chain relation (`cycle3_towerDefect_eq_zero_iff`) —
the first complete kernel computation of a defect matrix at carrier
level. In particular `C₃` is as far from Euler-factorizable as a
carrier can be: the failure is witnessed everywhere off the chains. -/

namespace Theaetetus

/-- **The sign on `C₃`, everywhere** (Q1 at the first carrier,
closed): the tower defect of the smallest rank-one carrier is
strictly negative at every incomparable pair of resolutions. -/
theorem cycle3_towerDefect_neg_of_incomparable (q q' : ℕ) [NeZero q] [NeZero q']
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    (cycleGraph 3 (by norm_num)).towerDefect q q' < 0 := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_neg_of_incomparable (by norm_num) hqq' hq'q

/-- **The kernel on `C₃`** (Q3 at the first carrier): the tower
defect vanishes exactly on chains — `C₃` is not Euler-factorizable,
and its defect matrix detects divisibility. -/
theorem cycle3_towerDefect_eq_zero_iff (q q' : ℕ) [NeZero q] [NeZero q'] :
    (cycleGraph 3 (by norm_num)).towerDefect q q' = 0 ↔ q ∣ q' ∨ q' ∣ q := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_eq_zero_iff (by norm_num)

/-! ## The classification, for every carrier

**Q3, closed at carrier level.** The saturation argument: at large
resolution only the modal class survives, so along the staircase of
coprime pairs `(n+1, n+2)` the tower defect converges to
`−log Z(1)` — strictly negative whenever the carrier has a cycle.
Hence the defect matrix of a carrier vanishes identically **iff**
its cycle lattice is trivial (`towerDefect_forall_eq_zero_iff`):
only the carriers with `b₁ = 0` are Euler-factorizable, exactly as
Q3 conjectured. On carriers with a cycle the sign of Q1 appears
asymptotically (`eventually_towerDefect_neg`) — in every rank. -/

namespace IncidenceGraph

universe u v

open Filter Topology

variable (G : IncidenceGraph.{u, v})

/-- The β-scaled class partition function, in Boltzmann-sum form. -/
private lemma classScaledPartFn_eq_tsum (β : ℝ) :
    G.classScaledPartFn β
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          Real.exp (-(β * G.harmonicEnergy κ)) := rfl

/-- **Saturation**: at infinite inverse temperature only the modal
class survives — the class Boltzmann sum tends to `1`, by dominated
convergence against the `β = 1` weight. -/
theorem tendsto_classScaledPartFn_atTop :
    Tendsto G.classScaledPartFn atTop (𝓝 1) := by
  classical
  have hb : Summable (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      Real.exp (-G.harmonicEnergy κ)) := G.classQuadAction.summable
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (β : ℝ) (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) =>
      Real.exp (-(β * G.harmonicEnergy κ)))
    (g := fun κ => if κ = 0 then (1 : ℝ) else 0)
    (bound := fun κ => Real.exp (-G.harmonicEnergy κ)) hb
    (by
      intro κ
      by_cases hκ : κ = 0
      · subst hκ
        simp only [G.harmonicEnergy_zero, mul_zero, neg_zero, Real.exp_zero]
        exact tendsto_const_nhds
      · simp only [if_neg hκ]
        have hE : 0 < G.harmonicEnergy κ := G.harmonicEnergy_pos hκ
        have h1 : Tendsto (fun β : ℝ => β * G.harmonicEnergy κ) atTop atTop :=
          (tendsto_mul_const_atTop_of_pos hE).mpr tendsto_id
        have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
        simpa only [Function.comp_def] using h2)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      intro κ
      have hE : 0 ≤ G.harmonicEnergy κ := G.classQuadAction.form_self_nonneg κ
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith)
  rw [tsum_ite_eq (0 : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
    (fun _ => (1 : ℝ))] at hlim
  exact hlim

/-- **The base complexity is positive on a carrier with a cycle**: a
nonzero class contributes strictly to the Boltzmann sum at any
inverse temperature. -/
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

/-- A carrier with trivial cycle lattice has trivial Boltzmann sums:
only the modal class contributes, at every inverse temperature. -/
theorem classScaledPartFn_eq_one_of_subsingleton
    [Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))] (β : ℝ) :
    G.classScaledPartFn β = 1 := by
  rw [classScaledPartFn_eq_tsum,
    tsum_eq_single 0 (fun κ hκ => absurd (Subsingleton.elim κ 0) hκ),
    G.harmonicEnergy_zero]
  simp

private lemma coprime_succ_succ (n : ℕ) : Nat.Coprime (n + 1) (n + 2) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

/-- **The saturation limit of the defect**: along the staircase of
coprime pairs `(n+1, n+2)` the tower defect converges to minus the
base complexity `−log Z(1)` — three of the four cross-ratio terms
saturate, and the shared trivial constraint remains. -/
theorem tendsto_towerDefect_succ :
    Tendsto (fun n : ℕ => G.towerDefect (n + 1) (n + 2)) atTop
      (𝓝 (-Real.log (G.classScaledPartFn 1))) := by
  have hzero : ∀ a : ℕ → ℕ, Tendsto a atTop atTop →
      Tendsto (fun n => Real.log (G.classScaledPartFn ((a n : ℝ) ^ 2))) atTop
        (𝓝 0) := by
    intro a ha
    have hcast : Tendsto (fun n => ((a n : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp ha
    have hsq : Tendsto (fun n => ((a n : ℝ)) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp hcast
    have hZ : Tendsto (fun n => G.classScaledPartFn ((a n : ℝ) ^ 2)) atTop
        (𝓝 1) := G.tendsto_classScaledPartFn_atTop.comp hsq
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hZ
    simpa only [Function.comp_def, Real.log_one] using hlog
  have hA := hzero (fun n => n + 1) (tendsto_add_atTop_nat 1)
  have hB := hzero (fun n => n + 2) (tendsto_add_atTop_nat 2)
  have hL := hzero (fun n => (n + 1) * (n + 2))
    (tendsto_atTop_mono (fun n => by nlinarith) (tendsto_add_atTop_nat 1))
  have hlaw : ∀ n : ℕ, G.towerDefect (n + 1) (n + 2)
      = (Real.log (G.classScaledPartFn (((n + 1 : ℕ) : ℝ) ^ 2))
          + Real.log (G.classScaledPartFn (((n + 2 : ℕ) : ℝ) ^ 2)))
        - (Real.log (G.classScaledPartFn 1)
          + Real.log (G.classScaledPartFn ((((n + 1) * (n + 2) : ℕ) : ℝ) ^ 2))) := by
    intro n
    have h := G.crossRatio_law (n + 1) (n + 2)
    rw [show Nat.gcd (n + 1) (n + 2) = 1 from coprime_succ_succ n,
      Nat.Coprime.lcm_eq_mul (coprime_succ_succ n)] at h
    simpa using h
  simp only [hlaw]
  have hlim := (hA.add hB).sub
    ((tendsto_const_nhds (x := Real.log (G.classScaledPartFn 1))).add hL)
  simpa using hlim

/-- **The sign appears asymptotically in every rank**: on a carrier
with a cycle, the tower defect is eventually strictly negative along
the staircase — Q1's sign, at the saturation end, for every carrier. -/
theorem eventually_towerDefect_neg
    (hnt : ∃ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ), κ ≠ 0) :
    ∀ᶠ n : ℕ in atTop, G.towerDefect (n + 1) (n + 2) < 0 := by
  have hpos : 0 < Real.log (G.classScaledPartFn 1) :=
    Real.log_pos (G.one_lt_classScaledPartFn one_pos hnt)
  exact G.tendsto_towerDefect_succ.eventually_lt_const (by linarith)

/-- **Q3, CLASSIFIED FOR EVERY CARRIER**: the defect matrix of a
carrier vanishes identically iff its cycle lattice is trivial — the
Euler-factorizable carriers are exactly those with `b₁ = 0`. One
direction is the saturation limit against a nonzero class; the other
is the collapse of every Boltzmann sum to the modal term. -/
theorem towerDefect_forall_eq_zero_iff :
    (∀ (q q' : ℕ) [NeZero q] [NeZero q'], G.towerDefect q q' = 0)
      ↔ Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) := by
  constructor
  · intro h
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have hnt : ∃ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ), κ ≠ 0 :=
      exists_ne 0
    have hpos : 0 < Real.log (G.classScaledPartFn 1) :=
      Real.log_pos (G.one_lt_classScaledPartFn one_pos hnt)
    have hlim := G.tendsto_towerDefect_succ
    rw [show (fun n : ℕ => G.towerDefect (n + 1) (n + 2)) = fun _ => 0 from
      funext fun n => h (n + 1) (n + 2)] at hlim
    have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
    linarith
  · intro hsub q q' _ _
    haveI := hsub
    rw [G.crossRatio_law q q',
      G.classScaledPartFn_eq_one_of_subsingleton,
      G.classScaledPartFn_eq_one_of_subsingleton,
      G.classScaledPartFn_eq_one_of_subsingleton,
      G.classScaledPartFn_eq_one_of_subsingleton]
    simp

end IncidenceGraph

end Theaetetus
