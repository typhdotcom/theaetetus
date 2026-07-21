-- ported from Meno/InfoRatchet.lean
import Theaetetus.SectorAction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Coarse-graining: fiber Boltzmann sums

Coarse-graining a sector action along a projection of its sector
type: each coarse sector is priced by the Boltzmann sum of its fiber,
and the partition function and complexity factorize through the
coarse-graining. Plus the counting lemma for constant-fiber maps. -/

namespace Theaetetus

open scoped BigOperators

universe u

/-- A map with constant fiber count `m` multiplies cardinalities. -/
theorem card_eq_card_mul_of_fiber {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) {m : ℕ}
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) :
    Fintype.card X = Fintype.card D * m := by
  rw [← Finset.card_univ (α := X),
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))]
  rw [Finset.sum_congr rfl fun d _ =>
    (show (Finset.univ.filter fun x : X => f x = d).card = m by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hfib d)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

namespace SectorAction

/-! ### Coarse-graining: fiber Boltzmann sums -/

/-- **The unnormalized coarse weight**: the Boltzmann sum
of a fiber of a projection — the total weight the fine action assigns
to a coarse sector. -/
noncomputable def coarseWeight (A : SectorAction.{u}) {B : Type u}
    (p : A.Λ → B) (b : B) : ℝ :=
  ∑' k : {k : A.Λ // p k = b}, A.weight k.val

/-- Fiber Boltzmann sums converge. -/
theorem summable_coarse (A : SectorAction.{u}) {B : Type u}
    (p : A.Λ → B) (b : B) :
    Summable (fun k : {k : A.Λ // p k = b} => A.weight k.val) :=
  A.summable.subtype _

/-- A coarse sector with a nonempty fiber carries positive weight. -/
theorem coarseWeight_pos (A : SectorAction.{u}) {B : Type u}
    {p : A.Λ → B} {b : B} (h : ∃ k, p k = b) :
    0 < A.coarseWeight p b := by
  obtain ⟨k₀, hk₀⟩ := h
  exact (A.summable_coarse p b).tsum_pos
    (fun k => A.weight_nonneg k.val) ⟨k₀, hk₀⟩ (A.weight_pos k₀)

/-- The coarse weights sum to the partition function — the fibers
partition the sector type. -/
theorem sum_coarseWeight (A : SectorAction.{u}) {B : Type u} [Fintype B]
    (p : A.Λ → B) : ∑ b, A.coarseWeight p b = A.partFn := by
  have hσ := (Equiv.summable_iff (Equiv.sigmaFiberEquiv p)).mpr A.summable
  calc ∑ b, A.coarseWeight p b
      = ∑' b : B, A.coarseWeight p b := (tsum_fintype _).symm
    _ = ∑' σ : Σ b : B, {k : A.Λ // p k = b}, A.weight σ.2.val :=
        hσ.tsum_sigma.symm
    _ = ∑' k : A.Λ, A.weight k := Equiv.tsum_eq (Equiv.sigmaFiberEquiv p) _

section CoarseGrain

variable (A : SectorAction.{u}) {B : Type u} [Fintype B] (p : A.Λ → B)
  (b₀ : B) (hpos : ∀ b, 0 < A.coarseWeight p b)
  (hmax : ∀ b, A.coarseWeight p b ≤ A.coarseWeight p b₀)

/-- **Coarse-graining a sector action**: project the
sector type along `p`, pricing each coarse sector by its fiber
Boltzmann sum. The energy is the effective free energy measured from
the modal sector `b₀` — nonnegative exactly because `b₀` is modal,
vanishing at `b₀`. -/
noncomputable def coarseGrain : SectorAction.{u} where
  Λ := B
  E b := Real.log (A.coarseWeight p b₀) - Real.log (A.coarseWeight p b)
  E_zero := ⟨b₀, sub_self _⟩
  E_nonneg b := sub_nonneg.mpr (Real.log_le_log (hpos b) (hmax b))
  summable := (hasSum_fintype _).summable

instance : Fintype (A.coarseGrain p b₀ hpos hmax).Λ :=
  inferInstanceAs (Fintype B)

/-- The coarse Boltzmann weight is the fiber-weight ratio against the
modal fiber. -/
theorem coarseGrain_weight (b : B) :
    (A.coarseGrain p b₀ hpos hmax).weight b
      = A.coarseWeight p b / A.coarseWeight p b₀ := by
  show Real.exp (-(Real.log (A.coarseWeight p b₀)
      - Real.log (A.coarseWeight p b))) = _
  rw [neg_sub, Real.exp_sub, Real.exp_log (hpos b), Real.exp_log (hpos b₀)]

/-- The coarse partition function: `Z_coarse = Z / W b₀`. -/
theorem coarseGrain_partFn :
    (A.coarseGrain p b₀ hpos hmax).partFn
      = A.partFn / A.coarseWeight p b₀ := by
  show (∑' b : B, (A.coarseGrain p b₀ hpos hmax).weight b) = _
  rw [tsum_fintype,
    Finset.sum_congr rfl fun b _ => coarseGrain_weight A p b₀ hpos hmax b,
    ← Finset.sum_div, A.sum_coarseWeight p]

/-- **The partition function factorizes through a coarse-graining**:
`Z = W b₀ · Z_coarse`. -/
theorem partFn_eq_coarseWeight_mul :
    A.partFn
      = A.coarseWeight p b₀ * (A.coarseGrain p b₀ hpos hmax).partFn := by
  rw [coarseGrain_partFn A p b₀ hpos hmax]
  have h0 : A.coarseWeight p b₀ ≠ 0 := (hpos b₀).ne'
  field_simp

/-- **The complexity decomposition through a coarse-graining**:
`log Z = log W b₀ + K_coarse`. -/
theorem complexity_eq_coarseGrain :
    A.complexity
      = Real.log (A.coarseWeight p b₀)
        + (A.coarseGrain p b₀ hpos hmax).complexity := by
  show Real.log A.partFn
    = _ + Real.log (A.coarseGrain p b₀ hpos hmax).partFn
  rw [coarseGrain_partFn A p b₀ hpos hmax,
    Real.log_div (ne_of_gt A.partFn_pos) (ne_of_gt (hpos b₀))]
  ring

end CoarseGrain

end SectorAction

end Theaetetus
