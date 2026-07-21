import Theaetetus.SectorAction
import Theaetetus.Theta
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Quadratic Action: the matrix layer

A `QuadraticAction r` is the analytic primitive whose sector lattice is
`Fin r → ℤ` and whose energy is `kᵀ Q k` for a symmetric positive-definite
Gram matrix `Q`. Summability of the Boltzmann weight is **derived** from
`Q.PosDef` (`summable_exp_neg_quadForm`, via the eigenvalue-free
coercivity bound `Matrix.PosDef.exists_coercivity`): it is a theorem
(`QuadraticAction.summable`), not a stored field.

The rank-1 case `ofScalar α hα` builds `QuadraticAction 1` with `Q = !![α]`;
its partition function equals `theta α = ∑' k : ℤ, exp(-α k²)`
(`ofScalar_partFn_eq`). The scalar layer — `theta`, its summability,
and the duality — lives in `Theaetetus/Theta.lean`. -/

namespace Theaetetus

open scoped BigOperators
open UpperHalfPlane Complex Matrix

universe u

/-! ## The summability engine, upstream of the structure

Scalar Gaussian sums, the product factorization over `ℤ^r`, coercivity
of positive-definite forms, and `summable_exp_neg_quadForm` — placed
*before* `QuadraticAction` so that summability of the Boltzmann weight
is **derived** from positive-definiteness, never stored. Coercivity
and `summable_exp_neg_quadForm` live upstream of
`Theaetetus/Periodization.lean`, which consumes them. -/

namespace QuadraticAction

/-- Summability of a product of independent non-negative summable
factors over `Fin r → ℤ`: the summability half of Fubini for counting
measure on `ℤ^r`. -/
theorem summable_finPi_prod (r : ℕ) (f : Fin r → ℤ → ℝ)
    (hf_nn : ∀ i z, 0 ≤ f i z)
    (hf_sum : ∀ i, Summable (f i)) :
    Summable (fun k : Fin r → ℤ => ∏ i, f i (k i)) := by
  induction r with
  | zero =>
    exact (hasSum_single default fun b hb =>
      absurd (Subsingleton.elim b default) hb).summable
  | succ n ih =>
    let e := Fin.succFunEquiv ℤ n
    set F : (Fin n → ℤ) → ℝ := fun q => ∏ i : Fin n, f (Fin.castSucc i) (q i)
    set G : ℤ → ℝ := f (Fin.last n)
    have hF_nn : ∀ q, 0 ≤ F q := fun q =>
      Finset.prod_nonneg (fun i _ => hf_nn (Fin.castSucc i) (q i))
    have hG_nn : ∀ z, 0 ≤ G z := hf_nn (Fin.last n)
    have hF_sum : Summable F :=
      ih (fun i => f (Fin.castSucc i))
        (fun i z => hf_nn (Fin.castSucc i) z)
        (fun i => hf_sum (Fin.castSucc i))
    have hG_sum : Summable G := hf_sum (Fin.last n)
    have hFG : Summable (fun p : (Fin n → ℤ) × ℤ => F p.1 * G p.2) :=
      summable_mul_of_summable_norm
        (hF_sum.congr fun q => (Real.norm_eq_abs (F q) ▸ abs_of_nonneg (hF_nn q)).symm)
        (hG_sum.congr fun z => (Real.norm_eq_abs (G z) ▸ abs_of_nonneg (hG_nn z)).symm)
    exact (e.summable_iff.mpr hFG).congr fun k =>
      (Fin.prod_univ_castSucc (fun i => f i (k i))).symm

end QuadraticAction

/-- The quadratic form of a matrix is continuous. Public: the Gaussian
family in `Theaetetus/Periodization.lean` also consumes it. -/
lemma continuous_quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : Fin d → ℝ => x ⬝ᵥ M.mulVec x) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

/-- **Coercivity**: a positive-definite form dominates a positive multiple
of the sum of squares. Eigenvalue-free: minimize on the compact unit
sphere of `∑ xᵢ²`, then scale by homogeneity. -/
theorem _root_.Matrix.PosDef.exists_coercivity {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin d → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ M.mulVec x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- rank 0: both sides are empty sums
    subst hd
    refine ⟨1, one_pos, fun x => ?_⟩
    simp [dotProduct]
  · -- the sphere S = {x | ∑ xᵢ² = 1} is compact and nonempty
    set S : Set (Fin d → ℝ) := {x | ∑ i, x i ^ 2 = 1} with hS
    have hcont_sq : Continuous (fun x : Fin d → ℝ => ∑ i, x i ^ 2) := by fun_prop
    have hclosed : IsClosed S := isClosed_eq hcont_sq continuous_const
    have hbdd : Bornology.IsBounded S := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at h1
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (x i), sq_abs (x i)]
    have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
    have hne : S.Nonempty := by
      refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
      simp [hS, Pi.single_apply]
    obtain ⟨x₀, hx₀S, hx₀min⟩ :=
      hcompact.exists_isMinOn hne (continuous_quadForm M).continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h0
      rw [hS] at hx₀S
      simp only [Set.mem_setOf_eq, h0, Pi.zero_apply] at hx₀S
      simp at hx₀S
    have hx₀pos : 0 < x₀ ⬝ᵥ M.mulVec x₀ := by
      have h := (posDef_iff_dotProduct_mulVec.mp hM).2 hx₀ne
      have hstar : star x₀ = x₀ := funext fun i => star_trivial _
      rwa [hstar] at h
    refine ⟨x₀ ⬝ᵥ M.mulVec x₀, hx₀pos, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx, Matrix.mulVec_zero, dotProduct_zero]
    · -- scale x to the sphere
      have hsum_pos : 0 < ∑ i, x i ^ 2 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
          ⟨i, Finset.mem_univ i,
            lt_of_le_of_ne (sq_nonneg (x i)) (Ne.symm (pow_ne_zero 2 hi))⟩
      set t : ℝ := Real.sqrt (∑ i, x i ^ 2) with ht
      have ht_pos : 0 < t := Real.sqrt_pos.mpr hsum_pos
      have ht_sq : t ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hsum_pos.le
      have hy : (t⁻¹ • x) ∈ S := by
        rw [hS]
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [← Finset.mul_sum, ← ht_sq]
        field_simp
      have hval : (t⁻¹ • x) ⬝ᵥ M.mulVec (t⁻¹ • x) = t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        simp [smul_eq_mul, sq]
        ring
      have := isMinOn_iff.mp hx₀min _ hy
      rw [hval] at this
      have h2 : (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 ≤ x ⬝ᵥ M.mulVec x := by
        have htne : t ≠ 0 := ne_of_gt ht_pos
        calc (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2
            ≤ (t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x)) * t ^ 2 := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
          _ = x ⬝ᵥ M.mulVec x := by field_simp
      calc (x₀ ⬝ᵥ M.mulVec x₀) * (∑ i, x i ^ 2)
          = (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 := by rw [ht_sq]
        _ ≤ x ⬝ᵥ M.mulVec x := h2

/-- Positive scalar multiples of positive-definite matrices are positive
definite. Hand-rolled: `Matrix.PosDef.smul` needs `StarOrderedRing ℝ`
synthesis, which fails at this pin. -/
lemma posDef_smul' {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (c • A)ᴴ = c • A
    rw [Matrix.conjTranspose_smul, star_trivial]
    congr 1
    exact (posDef_iff_dotProduct_mulVec.mp hA).1
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc ((posDef_iff_dotProduct_mulVec.mp hA).2 hx)

/-- Boltzmann weights of a positive-definite quadratic form are summable
over the integer lattice: `exp(-kᵀMk) ≤ ∏ᵢ exp(-c kᵢ²)` by coercivity,
and the right side is summable by the factorization machinery. -/
theorem summable_exp_neg_quadForm {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  have hquad : ∀ k : Fin d → ℤ,
      ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
        = (fun i => (k i : ℝ)) ⬝ᵥ M.mulVec (fun i => (k i : ℝ)) := by
    intro k
    show ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
      = ∑ i, (k i : ℝ) * ∑ j, M i j * (k j : ℝ)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (QuadraticAction.summable_finPi_prod d (fun _ z => Real.exp (-c * (z : ℝ) ^ 2))
      (fun _ z => (Real.exp_pos _).le)
      (fun _ => summable_theta c hc))
  calc Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))
      ≤ Real.exp (-(c * ∑ i, (k i : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, hquad k]
        exact hcoer _
    _ = ∏ i, Real.exp (-c * (k i : ℝ) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Over `ℝ`, a positive-definite matrix is symmetric: hermitian with
trivial star. -/
theorem _root_.Matrix.PosDef.isSymm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosDef) : A.IsSymm := by
  have h : Aᴴ = A := hA.1
  ext i j
  calc Aᵀ i j = A j i := rfl
    _ = star (A j i) := (star_trivial _).symm
    _ = Aᴴ i j := rfl
    _ = A i j := by rw [h]

/-- A quadratic action of rank `r`: a positive-definite Gram form
`Q : Matrix (Fin r) (Fin r) ℝ`. Symmetry (`QuadraticAction.Q_symm`)
and summability of the Boltzmann weight (`QuadraticAction.summable`)
are **derived**, never stored. -/
structure QuadraticAction (r : ℕ) where
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_posDef : Q.PosDef

namespace QuadraticAction

variable {r : ℕ} (A : QuadraticAction r)

/-- **Symmetry is a theorem**: positive-definiteness over
`ℝ` gives it. -/
theorem Q_symm : A.Q.IsSymm := A.Q_posDef.isSymm

/-- **Summability is a theorem**: the Boltzmann
weight of a quadratic action is summable, by coercivity of its
positive-definite Gram form. -/
theorem summable : Summable (fun k : Fin r → ℤ =>
    Real.exp (-(∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)))) :=
  summable_exp_neg_quadForm A.Q_posDef

/-- Energy at a sector: `E_Q(k) = ∑_{i,j} Q_ij · k_i · k_j`. -/
noncomputable def energy (k : Fin r → ℤ) : ℝ :=
  ∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)

theorem energy_zero : A.energy (0 : Fin r → ℤ) = 0 := by
  simp [energy]

/-- Quadratic energy as `xᵀ Q x` for the embedded real vector. -/
theorem energy_eq_dotProduct_mulVec (k : Fin r → ℤ) :
    A.energy k = (fun i => (k i : ℝ)) ⬝ᵥ A.Q.mulVec (fun i => (k i : ℝ)) := by
  show ∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)
    = ∑ i, (k i : ℝ) * ∑ j, A.Q i j * (k j : ℝ)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Quadratic energy is non-negative. -/
theorem energy_nonneg (k : Fin r → ℤ) : 0 ≤ A.energy k := by
  rw [A.energy_eq_dotProduct_mulVec]
  have hStar : (star (fun i : Fin r => (k i : ℝ))) = fun i => (k i : ℝ) := by
    funext i; exact star_trivial _
  have h := A.Q_posDef.posSemidef.dotProduct_mulVec_nonneg (fun i => (k i : ℝ))
  rw [hStar] at h; exact h

/-- The `SectorAction` packaging of a `QuadraticAction`. -/
noncomputable def toSectorAction : SectorAction.{0} where
  Λ := Fin r → ℤ
  E := A.energy
  E_zero := ⟨0, A.energy_zero⟩
  E_nonneg := A.energy_nonneg
  summable := A.summable

theorem partFn_eq : A.toSectorAction.partFn =
    ∑' k : Fin r → ℤ,
      Real.exp (-(∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ))) := rfl

/-- Two quadratic actions with the same Gram matrix have the same
partition function. The energy depends only on `Q`, so the Boltzmann
sums coincide pointwise. -/
theorem partFn_eq_of_Q_eq {r : ℕ} (A B : QuadraticAction r) (hQ : A.Q = B.Q) :
    A.toSectorAction.partFn = B.toSectorAction.partFn := by
  rw [A.partFn_eq, B.partFn_eq, hQ]

/-! ## Scalar quadratic action (rank 1) -/

/-- Scalar quadratic action at coupling `α > 0`: rank 1 with `Q = !![α]`. -/
noncomputable def ofScalar (α : ℝ) (hα : 0 < α) : QuadraticAction 1 where
  Q := !![α]
  Q_posDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · ext i j; fin_cases i; fin_cases j; rfl
    · intro x hx
      have hx0 : x 0 ≠ 0 := by
        intro h0; apply hx; ext i; fin_cases i; exact h0
      have hcomp : star x ⬝ᵥ !![α].mulVec x = α * (x 0)^2 := by
        simp [dotProduct, mulVec, Matrix.cons_val_fin_one, Pi.star_apply]
        ring
      rw [hcomp]
      have hsq : 0 < (x 0)^2 := by positivity
      exact mul_pos hα hsq

/-- Partition function of the scalar quadratic action equals
`theta α`. -/
theorem ofScalar_partFn_eq (α : ℝ) (hα : 0 < α) :
    (ofScalar α hα).toSectorAction.partFn = theta α := by
  show ∑' k : Fin 1 → ℤ, Real.exp (-(ofScalar α hα).energy k)
    = ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)
  have henergy : ∀ k : Fin 1 → ℤ, (ofScalar α hα).energy k = α * (k 0 : ℝ)^2 := by
    intro k
    show ∑ i : Fin 1, ∑ j : Fin 1,
        (ofScalar α hα).Q i j * (k i : ℝ) * (k j : ℝ) = α * (k 0 : ℝ)^2
    show ∑ i : Fin 1, ∑ j : Fin 1, !![α] i j * (k i : ℝ) * (k j : ℝ) = α * (k 0 : ℝ)^2
    simp [Matrix.cons_val_fin_one]
    ring
  have hrewrite : (fun k : Fin 1 → ℤ => Real.exp (-(ofScalar α hα).energy k))
      = (fun k : Fin 1 → ℤ => Real.exp (-α * (k 0 : ℝ)^2)) := by
    funext k; rw [henergy k]; ring_nf
  rw [hrewrite]
  let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
  exact e.tsum_eq (fun n : ℤ => Real.exp (-α * (n : ℝ) ^ 2))

/-- Half-power of a product of non-negative reals, complex `cpow` form:
`∏ᵢ (fᵢ)^(1/2) = (∏ᵢ fᵢ)^(1/2)`. Public: also used by
`Theaetetus/Periodization.lean`. -/
lemma prod_cpow_half : ∀ (r : ℕ) (f : Fin r → ℝ), (∀ i, 0 ≤ f i) →
    ∏ i, (↑(f i) : ℂ) ^ ((1 : ℂ) / 2) = (↑(∏ i, f i) : ℂ) ^ ((1 : ℂ) / 2)
  | 0, f, _ => by simp
  | (n + 1), f, hf => by
    rw [Fin.prod_univ_castSucc (f := fun i => (↑(f i) : ℂ) ^ ((1 : ℂ) / 2)),
        Fin.prod_univ_castSucc (f := f),
        prod_cpow_half n (fun i => f (Fin.castSucc i)) (fun i => hf _),
        Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg
          (Finset.prod_nonneg fun i _ => hf _) (hf _)]

end QuadraticAction

end Theaetetus
