import Theaetetus.Certification

/-! # Certified shell counts

Coercivity confines energy sublevel sets of a quadratic action to
sup-norm boxes: when `R < μ·(N+1)²` for a certified eigenvalue
lower bound `μ > 0`, every sector of energy at most `R` has all
coordinates bounded by `N` (`QuadraticAction.abs_le_of_energy_le`),
so the sublevel set lands inside the box
(`QuadraticAction.energy_sublevel_subset_box`), is finite
(`QuadraticAction.finite_energy_sublevel`), and carries at most
`(2N+1)^r` sectors (`QuadraticAction.energy_sublevel_ncard_le`).
Every energy shell — a level set of the energy — obeys the same
bound (`QuadraticAction.energy_shell_ncard_le`). -/

namespace Theaetetus

open Matrix

variable {r : ℕ}

/-- **Box confinement**: below energy `R`, every coordinate of a
sector is at most `N` once `R < μ·(N+1)²`. -/
theorem QuadraticAction.abs_le_of_energy_le (A : QuadraticAction r)
    {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) {k : Fin r → ℤ}
    (hk : A.energy k ≤ R) (i : Fin r) :
    |k i| ≤ (N : ℤ) := by
  by_contra h
  push Not at h
  have h1 : (N : ℤ) + 1 ≤ |k i| := by omega
  have h2 : ((N : ℝ) + 1) ≤ |(k i : ℝ)| := by exact_mod_cast h1
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ (k i : ℝ) ^ 2 := by
    nlinarith [abs_nonneg ((k i : ℝ)), sq_abs ((k i : ℝ)),
      (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have hle : ((k i : ℝ)) ^ 2 ≤ ∑ j, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ)))
      (Finset.mem_univ i)
  have hE := A.mul_sum_sq_le_energy hμ k
  linarith [mul_le_mul_of_nonneg_left hsq hμ0.le,
    mul_le_mul_of_nonneg_left hle hμ0.le]

/-- The sublevel set lands inside the box `Finset`. -/
theorem QuadraticAction.energy_sublevel_subset_box
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k ≤ R}
      ⊆ ↑(Fintype.piFinset fun _ : Fin r =>
          Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
  intro k hk
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc, ← abs_le]
  exact A.abs_le_of_energy_le hμ0 hμ hRN hk i

/-- **Sublevel finiteness**, with the box as the certificate. -/
theorem QuadraticAction.finite_energy_sublevel
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k ≤ R}.Finite :=
  (Fintype.piFinset fun _ : Fin r =>
    Finset.Icc (-(N : ℤ)) (N : ℤ)).finite_toSet.subset
      (A.energy_sublevel_subset_box hμ0 hμ hRN)

/-- **The certified sublevel count**: at most `(2N+1)^r` sectors
below energy `R`. -/
theorem QuadraticAction.energy_sublevel_ncard_le
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k ≤ R}.ncard ≤ (2 * N + 1) ^ r := by
  calc {k : Fin r → ℤ | A.energy k ≤ R}.ncard
      ≤ (↑(Fintype.piFinset fun _ : Fin r =>
          Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set (Fin r → ℤ)).ncard :=
        Set.ncard_le_ncard (A.energy_sublevel_subset_box hμ0 hμ hRN)
          (Finset.finite_toSet _)
    _ = (2 * N + 1) ^ r := by
        rw [Set.ncard_coe_finset, Fintype.card_piFinset_const]
        congr 1
        rw [Int.card_Icc]
        omega

/-- **The certified shell count**: every energy level set obeys the
same box bound. -/
theorem QuadraticAction.energy_shell_ncard_le
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k = R}.ncard ≤ (2 * N + 1) ^ r :=
  le_trans
    (Set.ncard_le_ncard (fun _ hk => le_of_eq hk)
      (A.finite_energy_sublevel hμ0 hμ hRN))
    (A.energy_sublevel_ncard_le hμ0 hμ hRN)

end Theaetetus
