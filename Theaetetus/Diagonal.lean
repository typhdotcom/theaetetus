import Theaetetus.Submodular

/-! # Diagonal forms: the sign in every rank

Q1 extends beyond rank one by pure arithmetic. The Boltzmann sum of
an orthogonal sum of rank-one lattices is the product of its axis
theta factors, so log partition functions add, and the defect of the
positive diagonal form `Q(x) = c₁x₁² + ⋯ + c_r x_r²` is the **sum of
rank-one defects**, one per axis at scale `cᵢ·s`
(`diagDefect_eq_sum`). The rank-one sign theorem then closes the
sign for every diagonal form in every rank `r ≥ 1`: strictly
negative at every incomparable pair
(`diagDefect_neg_of_incomparable`), zero exactly on chains
(`diagDefect_eq_zero_iff`).

The open frontier of Q1 is therefore not rank — it is
indecomposability: forms with genuine cross terms, where the
partition function does not factor over the axes. -/

namespace Theaetetus

/-- The Boltzmann sum of the positive diagonal form
`Q(x) = ∑ᵢ cᵢxᵢ²` on `ℤʳ` at coupling `t`: the product of the axis
theta factors — the analytic content of the orthogonal-sum
factorization `Z_{L₁⊥L₂} = Z_{L₁}·Z_{L₂}`. -/
noncomputable def diagTheta {r : ℕ} (c : Fin r → ℝ) (t : ℝ) : ℝ :=
  ∏ i, theta (c i * t)

/-- **The defect of a diagonal form**: the four-term
inclusion–exclusion of log Boltzmann sums over the interval
`[gcd, lcm]` of the divisibility lattice, exactly as at rank one. -/
noncomputable def diagDefect {r : ℕ} (c : Fin r → ℝ) (s : ℝ) (q q' : ℕ) : ℝ :=
  (Real.log (diagTheta c ((q : ℝ) ^ 2 * s))
      + Real.log (diagTheta c ((q' : ℝ) ^ 2 * s)))
    - (Real.log (diagTheta c ((Nat.gcd q q' : ℝ) ^ 2 * s))
      + Real.log (diagTheta c ((Nat.lcm q q' : ℝ) ^ 2 * s)))

variable {r : ℕ} {c : Fin r → ℝ} {s : ℝ}

private lemma log_diagTheta (hc : ∀ i, 0 < c i) {t : ℝ} (ht : 0 < t) :
    Real.log (diagTheta c t) = ∑ i, Real.log (theta (c i * t)) :=
  Real.log_prod fun i _ => (theta_pos _ (mul_pos (hc i) ht)).ne'

/-- **Additivity over the axes**: the diagonal defect is the sum of
rank-one defects at the axis scales `cᵢ·s` — orthogonal sums add
defects. -/
theorem diagDefect_eq_sum (hc : ∀ i, 0 < c i) (hs : 0 < s) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    diagDefect c s q q' = ∑ i, defect (c i * s) q q' := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq'
  have hg : Nat.gcd q q' ≠ 0 := fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hl : Nat.lcm q q' ≠ 0 := Nat.lcm_ne_zero hq hq'
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hg
  have hlR : (0 : ℝ) < (Nat.lcm q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hl
  unfold diagDefect
  rw [log_diagTheta hc (by positivity), log_diagTheta hc (by positivity),
    log_diagTheta hc (by positivity), log_diagTheta hc (by positivity),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold defect
  rw [show c i * ((q : ℝ) ^ 2 * s) = (q : ℝ) ^ 2 * (c i * s) from by ring,
    show c i * ((q' : ℝ) ^ 2 * s) = (q' : ℝ) ^ 2 * (c i * s) from by ring,
    show c i * ((Nat.gcd q q' : ℝ) ^ 2 * s)
      = (Nat.gcd q q' : ℝ) ^ 2 * (c i * s) from by ring,
    show c i * ((Nat.lcm q q' : ℝ) ^ 2 * s)
      = (Nat.lcm q q' : ℝ) ^ 2 * (c i * s) from by ring]

/-- The diagonal defect vanishes on chains — identically in the
weights, no positivity needed. -/
theorem diagDefect_eq_zero_of_dvd (c : Fin r → ℝ) (s : ℝ) {q q' : ℕ}
    (hdvd : q ∣ q') : diagDefect c s q q' = 0 := by
  unfold diagDefect
  rw [Nat.gcd_eq_left hdvd,
    Nat.dvd_antisymm (Nat.lcm_dvd hdvd dvd_rfl) (Nat.dvd_lcm_right q q')]
  ring

/-- The diagonal defect is symmetric in its resolutions. -/
theorem diagDefect_comm (c : Fin r → ℝ) (s : ℝ) (q q' : ℕ) :
    diagDefect c s q q' = diagDefect c s q' q := by
  unfold diagDefect
  rw [Nat.gcd_comm, Nat.lcm_comm]
  ring

/-- **Q1 for diagonal forms, every rank**: the defect of a positive
diagonal form of any rank `r ≥ 1` is strictly negative at every
incomparable pair and every scale — each axis contributes a strictly
negative rank-one defect, and orthogonality adds them. -/
theorem diagDefect_neg_of_incomparable (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    (hs : 0 < s) {q q' : ℕ} (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    diagDefect c s q q' < 0 := by
  have hq : q ≠ 0 := fun h => hq'q (by rw [h]; exact dvd_zero q')
  have hq' : q' ≠ 0 := fun h => hqq' (by rw [h]; exact dvd_zero q)
  rw [diagDefect_eq_sum hc hs hq hq']
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  exact Finset.sum_neg
    (fun i _ => defect_neg_of_incomparable (mul_pos (hc i) hs) hqq' hq'q)
    Finset.univ_nonempty

/-- The sign never reverses: the diagonal defect is nonpositive at
every pair and every rank (rank zero included — there it vanishes
identically, the empty product). -/
theorem diagDefect_nonpos (hc : ∀ i, 0 < c i) (hs : 0 < s) (q q' : ℕ) :
    diagDefect c s q q' ≤ 0 := by
  by_cases hqq' : q ∣ q'
  · exact (diagDefect_eq_zero_of_dvd c s hqq').le
  by_cases hq'q : q' ∣ q
  · rw [diagDefect_comm]
    exact (diagDefect_eq_zero_of_dvd c s hq'q).le
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [diagDefect, diagTheta]
  · exact (diagDefect_neg_of_incomparable hr.ne' hc hs hqq' hq'q).le

/-- **The kernel, diagonal forms**: the defect vanishes exactly on
chains — every positive diagonal form of rank `r ≥ 1` detects
divisibility. -/
theorem diagDefect_eq_zero_iff (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    (hs : 0 < s) {q q' : ℕ} :
    diagDefect c s q q' = 0 ↔ q ∣ q' ∨ q' ∣ q := by
  constructor
  · intro h0
    by_contra hcon
    push_neg at hcon
    exact absurd h0 (diagDefect_neg_of_incomparable hr hc hs hcon.1 hcon.2).ne
  · rintro (hdvd | hdvd)
    · exact diagDefect_eq_zero_of_dvd c s hdvd
    · rw [diagDefect_comm]
      exact diagDefect_eq_zero_of_dvd c s hdvd

end Theaetetus
