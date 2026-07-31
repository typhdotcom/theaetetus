import Theaetetus.QuadraticAction
import Mathlib.Analysis.Matrix.PosDef

/-! # Certified coercivity: the least Gram eigenvalue

`Matrix.PosDef.exists_coercivity` produces its constant by
compactness and leaves it anonymous. This module pins the constant
to the spectrum and makes it checkable.

The spectral half: any uniform lower bound `μ` on the eigenvalues
of a real symmetric matrix bounds the quadratic form below by
`μ·∑xᵢ²` (`Matrix.IsHermitian.mul_sum_sq_le_quadForm`), and
conversely every coercivity constant is at most every eigenvalue
(`Matrix.IsHermitian.le_eigenvalues_of_mul_sum_sq_le`): `μ` is a
coercivity constant iff it lower-bounds every eigenvalue
(`Matrix.IsHermitian.mul_sum_sq_le_quadForm_iff`).

The checkable half: row dominance — `μ + ∑_{j ≠ i} |M i j| ≤ M i i`
in every row, a finite kernel-checkable system of inequalities in
the entries, rational arithmetic when the entries are rational —
forces the same lower bound
(`mul_sum_sq_le_quadForm_of_dominant`), gives positive
definiteness when the margin is positive (`posDef_of_dominant`),
and pushes `μ` below the whole spectrum
(`le_eigenvalues_of_dominant`). This is the Gershgorin disc bound
in quadratic-form clothing: a certified eigenvalue bound for a
concrete Gram matrix reduces to inequalities the kernel checks.
Through `QuadraticAction.mul_sum_sq_le_energy` the bound transfers
to lattice energies, where it dominates Boltzmann tails. -/

namespace Theaetetus

open Matrix

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- Over `ℝ`, the star of a matrix is its transpose. -/
private lemma star_eq_transpose (A : Matrix (Fin d) (Fin d) ℝ) :
    star A = Aᵀ := by
  ext i j
  rw [Matrix.star_apply, Matrix.transpose_apply, star_trivial]

/-! ## The spectral half: the form in the eigenbasis -/

/-- **The quadratic form diagonalized**: rotating a real symmetric
matrix by its eigenvector unitary turns `xᵀMx` into
eigenvalue-weighted squares. -/
theorem _root_.Matrix.IsHermitian.quadForm_eq_eigen_sum
    (hM : M.IsHermitian) (x : Fin d → ℝ) :
    x ⬝ᵥ M.mulVec x
      = ∑ i, hM.eigenvalues i
          * Matrix.vecMul x
              (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) i ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℝ :=
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  set Dv : Fin d → ℝ := hM.eigenvalues with hDv
  have hspec : M = U * Matrix.diagonal Dv * star U := by
    have h := Matrix.IsHermitian.spectral_theorem hM
    rwa [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
      Function.id_comp] at h
  calc x ⬝ᵥ M.mulVec x
      = x ⬝ᵥ (U * Matrix.diagonal Dv * star U).mulVec x := by rw [← hspec]
    _ = x ⬝ᵥ (U * Matrix.diagonal Dv).mulVec ((star U).mulVec x) := by
        rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ (U * Matrix.diagonal Dv).mulVec (Matrix.vecMul x U) := by
        rw [star_eq_transpose, Matrix.mulVec_transpose]
    _ = Matrix.vecMul x (U * Matrix.diagonal Dv) ⬝ᵥ Matrix.vecMul x U :=
        Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.vecMul (Matrix.vecMul x U) (Matrix.diagonal Dv)
          ⬝ᵥ Matrix.vecMul x U := by
        rw [← Matrix.vecMul_vecMul]
    _ = ∑ i, Dv i * Matrix.vecMul x U i ^ 2 := by
        show ∑ i, Matrix.vecMul (Matrix.vecMul x U) (Matrix.diagonal Dv) i
            * Matrix.vecMul x U i = _
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.vecMul_diagonal]
        ring

/-- **The rotation preserves the sum of squares**: the eigenvector
unitary of a real symmetric matrix is orthogonal. -/
theorem _root_.Matrix.IsHermitian.sum_sq_vecMul_eigenvectorUnitary
    (hM : M.IsHermitian) (x : Fin d → ℝ) :
    ∑ i, Matrix.vecMul x
        (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) i ^ 2
      = ∑ i, x i ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℝ :=
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  have hUstar : U * star U = 1 := by
    rw [hU, ← Unitary.coe_star]
    exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
  simp only [pow_two]
  show Matrix.vecMul x U ⬝ᵥ Matrix.vecMul x U = x ⬝ᵥ x
  calc Matrix.vecMul x U ⬝ᵥ Matrix.vecMul x U
      = Matrix.vecMul x U ⬝ᵥ Uᵀ.mulVec x := by
        rw [Matrix.mulVec_transpose]
    _ = Matrix.vecMul (Matrix.vecMul x U) Uᵀ ⬝ᵥ x :=
        Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.vecMul x (U * Uᵀ) ⬝ᵥ x := by rw [Matrix.vecMul_vecMul]
    _ = x ⬝ᵥ x := by
        rw [← star_eq_transpose U, hUstar, Matrix.vecMul_one]

/-- **Coercivity at the least Gram eigenvalue**: a uniform lower
bound `μ` on the eigenvalues of a real symmetric matrix bounds its
quadratic form below by `μ·∑xᵢ²`. -/
theorem _root_.Matrix.IsHermitian.mul_sum_sq_le_quadForm
    (hM : M.IsHermitian) {μ : ℝ} (hμ : ∀ i, μ ≤ hM.eigenvalues i)
    (x : Fin d → ℝ) :
    μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x := by
  rw [hM.quadForm_eq_eigen_sum x,
    ← hM.sum_sq_vecMul_eigenvectorUnitary x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hμ i) (sq_nonneg _)

/-- **Sharpness**: every coercivity constant of the quadratic form
is at most every eigenvalue. Witnessed by rotating a coordinate
vector into the eigenbasis. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues_of_mul_sum_sq_le
    (hM : M.IsHermitian) {μ : ℝ}
    (h : ∀ x : Fin d → ℝ, μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x)
    (i : Fin d) :
    μ ≤ hM.eigenvalues i := by
  have hstarU : star (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
      * (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) = 1 := by
    rw [← Unitary.coe_star]
    exact Unitary.coe_star_mul_self hM.eigenvectorUnitary
  set x : Fin d → ℝ :=
    (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ).mulVec
      (Pi.single i 1) with hx
  have hvec : Matrix.vecMul x
      (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
      = Pi.single i 1 := by
    rw [hx, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      ← star_eq_transpose, hstarU, Matrix.one_mulVec]
  have hval := h x
  rw [hM.quadForm_eq_eigen_sum x, hvec] at hval
  have hnorm : ∑ j, x j ^ 2 = 1 := by
    rw [← hM.sum_sq_vecMul_eigenvectorUnitary x, hvec,
      Fintype.sum_eq_single i]
    · rw [Pi.single_eq_same]
      norm_num
    · intro b hb
      rw [Pi.single_eq_of_ne hb]
      ring
  have heig : ∑ j, hM.eigenvalues j * (Pi.single i 1 : Fin d → ℝ) j ^ 2
      = hM.eigenvalues i := by
    rw [Fintype.sum_eq_single i]
    · rw [Pi.single_eq_same]
      ring
    · intro b hb
      rw [Pi.single_eq_of_ne hb]
      ring
  rw [hnorm, heig] at hval
  linarith

/-- **The coercivity criterion**: `μ` is a coercivity constant for
the quadratic form of a real symmetric matrix iff it is a lower
bound for every eigenvalue. -/
theorem _root_.Matrix.IsHermitian.mul_sum_sq_le_quadForm_iff
    (hM : M.IsHermitian) {μ : ℝ} :
    (∀ x : Fin d → ℝ, μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x)
      ↔ ∀ i, μ ≤ hM.eigenvalues i :=
  ⟨hM.le_eigenvalues_of_mul_sum_sq_le,
    fun hμ x => hM.mul_sum_sq_le_quadForm hμ x⟩

/-! ## The checkable half: row dominance -/

/-- **The dominance certificate**: for a symmetric matrix, the row
bounds `μ + ∑_{j ≠ i} |M i j| ≤ M i i` — finitely many inequalities
in the entries — force the quadratic form to dominate `μ·∑xᵢ²`. The
off-diagonal mass is absorbed pairwise through
`|Mᵢⱼ·xᵢ·xⱼ| ≤ |Mᵢⱼ|·(xᵢ² + xⱼ²)/2`, and symmetry folds the two
halves onto the rows. -/
theorem mul_sum_sq_le_quadForm_of_dominant (hsym : M.IsSymm) {μ : ℝ}
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i)
    (x : Fin d → ℝ) :
    μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x := by
  have hexpand : x ⬝ᵥ M.mulVec x
      = ∑ i, (M i i * x i ^ 2
          + ∑ j ∈ Finset.univ.erase i, M i j * (x i * x j)) := by
    show (∑ i, x i * ∑ j, M i j * x j) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ (fun j => M i j * x j)
        (Finset.mem_univ i), mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hcross : ∀ i,
      -(∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2) / 2)
        ≤ ∑ j ∈ Finset.univ.erase i, M i j * (x i * x j) := by
    intro i
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have habs : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hlow := neg_abs_le (M i j * (x i * x j))
    rw [abs_mul] at hlow
    nlinarith [hlow, mul_le_mul_of_nonneg_left habs (abs_nonneg (M i j))]
  have hswap : (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2)
      = ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2 := by
    have hcomm : (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2)
        = ∑ j, ∑ i ∈ Finset.univ.erase j, |M i j| * x j ^ 2 :=
      Finset.sum_comm' fun i j => by
        simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        exact ne_comm
    have hMsym : Mᵀ = M := hsym
    rw [hcomm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hab : M b a = M a b := by
      calc M b a = Mᵀ a b := rfl
        _ = M a b := by rw [hMsym]
    rw [hab]
  have hA : (∑ i, ∑ j ∈ Finset.univ.erase i,
        |M i j| * (x i ^ 2 + x j ^ 2) / 2)
      = ∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2 := by
    have hhalf : ∀ i,
        (∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2) / 2)
          = ((∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
              + ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2) / 2 := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    calc (∑ i, ∑ j ∈ Finset.univ.erase i,
          |M i j| * (x i ^ 2 + x j ^ 2) / 2)
        = ∑ i, ((∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
            + ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2) / 2 :=
          Finset.sum_congr rfl fun i _ => hhalf i
      _ = ((∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
            + ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2 := by
          rw [hswap]
          ring
      _ = ∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  have h2 : -(∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2)
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, M i j * (x i * x j) := by
    rw [← hA, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hcross i
  have h1 : (∑ i, μ * x i ^ 2)
        + ∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2
      ≤ ∑ i, M i i * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hdom i, sq_nonneg (x i)]
  calc μ * ∑ i, x i ^ 2
      = ∑ i, μ * x i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ x ⬝ᵥ M.mulVec x := by
        rw [hexpand, Finset.sum_add_distrib]
        linarith [h1, h2]

/-- **Positive definiteness from strict dominance**: a symmetric
matrix whose rows are dominant with positive margin is positive
definite. -/
theorem posDef_of_dominant (hsym : M.IsSymm) {μ : ℝ} (hμ : 0 < μ)
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i) :
    M.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_iff_isSymm.mpr hsym, fun x hx => ?_⟩
  have hstar : star x = x := funext fun i => star_trivial _
  rw [hstar]
  have hsum_pos : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i, Finset.mem_univ i,
        lt_of_le_of_ne (sq_nonneg (x i)) (Ne.symm (pow_ne_zero 2 hi))⟩
  calc (0 : ℝ) < μ * ∑ i, x i ^ 2 := mul_pos hμ hsum_pos
    _ ≤ x ⬝ᵥ M.mulVec x := mul_sum_sq_le_quadForm_of_dominant hsym hdom x

/-- **The certified spectral lower bound**: row dominance pushes
`μ` below every eigenvalue — a bound on the spectrum reduced to
finitely many entrywise inequalities, rational arithmetic when
the entries are rational. -/
theorem le_eigenvalues_of_dominant (hM : M.IsHermitian) {μ : ℝ}
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i)
    (i : Fin d) :
    μ ≤ hM.eigenvalues i :=
  hM.le_eigenvalues_of_mul_sum_sq_le
    (fun x => mul_sum_sq_le_quadForm_of_dominant
      (isHermitian_iff_isSymm.mp hM) hdom x) i

/-- **Coercivity of the lattice energy**: a certified lower bound on
the Gram eigenvalues bounds the energy of a quadratic action below
by `μ·∑kᵢ²` on every sector. -/
theorem QuadraticAction.mul_sum_sq_le_energy {r : ℕ}
    (A : QuadraticAction r) {μ : ℝ}
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (k : Fin r → ℤ) :
    μ * ∑ i, (k i : ℝ) ^ 2 ≤ A.energy k := by
  rw [A.energy_eq_dotProduct_mulVec]
  exact A.Q_posDef.1.mul_sum_sq_le_quadForm hμ _

end Theaetetus
