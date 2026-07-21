-- ported from Meno/SectorAction.lean
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Sector Action: the analytic primitive

A `SectorAction` is a sector type `Λ`, a non-negative energy
`E : Λ → ℝ` attaining zero somewhere, and summability of the
Boltzmann weight `exp(-E k)`. From this we derive the partition
function `Z = ∑' exp(-E)`, the complexity `K = log Z`, the Gibbs
density `μ = exp(-E) / Z` (a probability on `Λ`), the expectation
`⟨f⟩`, the variance `Var(f) = ⟨f²⟩ - ⟨f⟩²`, and the cumulant
functional `cgf`.

Ported minimally per the copy-map (PROGRAM.md): the primitive and
its foundational positivity lemmas. Combinators and fluctuation
theory stay in the quarry until needed. -/

namespace Theaetetus

universe u

open scoped BigOperators

/-- A sector action: a sector type `Λ` with a non-negative energy `E`
attaining zero, whose Boltzmann weight `exp(-E)` is summable. -/
structure SectorAction where
  Λ : Type u
  E : Λ → ℝ
  E_zero : ∃ z : Λ, E z = 0
  E_nonneg : ∀ k, 0 ≤ E k
  summable : Summable (fun k => Real.exp (-E k))

namespace SectorAction

variable (A : SectorAction.{u})

/-- Boltzmann weight at sector `k`: `exp(-E k)`. -/
noncomputable def weight (k : A.Λ) : ℝ := Real.exp (-A.E k)

theorem weight_pos (k : A.Λ) : 0 < A.weight k := Real.exp_pos _

theorem weight_nonneg (k : A.Λ) : 0 ≤ A.weight k := (A.weight_pos k).le

/-- Partition function `Z = ∑' k, exp(-E k)`. -/
noncomputable def partFn : ℝ := ∑' k, A.weight k

/-- Complexity `K = log Z`. -/
noncomputable def complexity : ℝ := Real.log A.partFn

/-- Gibbs density `μ k = exp(-E k) / Z`. -/
noncomputable def gibbsMass (k : A.Λ) : ℝ := A.weight k / A.partFn

/-- Gibbs expectation of an observable `f : Λ → ℝ`. -/
noncomputable def gibbsExpect (f : A.Λ → ℝ) : ℝ := ∑' k, f k * A.gibbsMass k

/-- Gibbs variance of an observable: `⟨f²⟩ - ⟨f⟩²`. -/
noncomputable def gibbsVariance (f : A.Λ → ℝ) : ℝ :=
  A.gibbsExpect (fun k => f k ^ 2) - A.gibbsExpect f ^ 2

/-- **The cumulant functional** of the Gibbs law: the log
Gibbs-mean of the exponentiated observable, `log ⟨e^φ⟩` —
unconditioned, like `partFn` and `gibbsExpect`; each law carries its
own summability, and on a finite `Λ` it is automatic. -/
noncomputable def cgf (φ : A.Λ → ℝ) : ℝ :=
  Real.log (A.gibbsExpect fun k => Real.exp (φ k))

/-! ## Foundational lemmas -/

/-- The partition function is strictly positive: the zero-energy witness
contributes a positive term to a summable, non-negative series. -/
theorem partFn_pos : 0 < A.partFn := by
  obtain ⟨z, _⟩ := A.E_zero
  exact A.summable.tsum_pos (fun k => A.weight_nonneg k) z (A.weight_pos z)

/-- The Gibbs density is non-negative. -/
theorem gibbsMass_nonneg (k : A.Λ) : 0 ≤ A.gibbsMass k :=
  div_nonneg (A.weight_nonneg k) A.partFn_pos.le

/-- The Gibbs density is strictly positive: every sector carries
weight. -/
theorem gibbsMass_pos (k : A.Λ) : 0 < A.gibbsMass k :=
  div_pos (A.weight_pos k) A.partFn_pos

/-- The Gibbs density is summable. -/
theorem summable_gibbsMass : Summable A.gibbsMass := by
  show Summable (fun k => A.weight k / A.partFn)
  exact A.summable.div_const _

/-- The Gibbs density integrates to 1: it is a probability density on `Λ`. -/
theorem tsum_gibbsMass_eq_one : ∑' k, A.gibbsMass k = 1 := by
  show ∑' k, A.weight k / A.partFn = 1
  rw [tsum_div_const]
  exact div_self (ne_of_gt A.partFn_pos)

end SectorAction

end Theaetetus
