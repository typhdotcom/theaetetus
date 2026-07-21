import Theaetetus.Submodular

/-! # The factorization reading: the defect as conditional association

The probabilistic content of the sign, made exact. Under the Gibbs
weight `exp(−sk²)/θ(s)` on `ℤ`, the **divisibility event** `q ∣ X`
has mass `resProb s q = θ(q²s)/θ(s)` — a theorem about the
sublattice `qℤ`, not a definition (`resProb_eq_event_mass`, through
the reindexing `theta_sq_eq_tsum_dvd`).

Minus the defect is then exactly the log of the conditional
association ratio of the two divisibility events — joint over
product of marginals, conditioned on the shared constraint
(`exp_defect_eq`, `defect_eq_log_ratio`, `neg_defect_eq_log_assoc`):
CRT factors the state space, and the defect prices the failure of
the Gibbs measure to follow — the conditional pointwise mutual
information of the two events at their shared constraint, with the
sign convention that positive association means negative defect. The sign theorem becomes a
correlation statement: conditioned on the common resolution, the
events are strictly positively associated
(`condProb_mul_lt_of_incomparable`); unconditionally, coprime
divisibility events are strictly positively correlated
(`resProb_mul_lt_of_coprime`); and the association vanishes exactly
on chains (`resProb_mul_eq_iff`). -/

namespace Theaetetus

/-- **The divisibility-event mass**: the Gibbs probability of
`q ∣ X` at scale `s`, as a theta ratio. -/
noncomputable def resProb (s : ℝ) (q : ℕ) : ℝ :=
  theta ((q : ℝ) ^ 2 * s) / theta s

theorem resProb_pos {s : ℝ} (hs : 0 < s) {q : ℕ} (hq : q ≠ 0) :
    0 < resProb s q := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  exact div_pos (theta_pos _ (by positivity)) (theta_pos _ hs)

theorem resProb_le_one {s : ℝ} (hs : 0 < s) {q : ℕ} (hq : q ≠ 0) :
    resProb s q ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  have hle : s ≤ (q : ℝ) ^ 2 * s :=
    le_mul_of_one_le_left hs.le (by nlinarith)
  exact (div_le_one (theta_pos s hs)).mpr (theta_anti hs hle)

/-- The trivial resolution is the sure event. -/
theorem resProb_one {s : ℝ} (hs : 0 < s) : resProb s 1 = 1 := by
  rw [resProb, show ((1 : ℕ) : ℝ) ^ 2 * s = s from by norm_num]
  exact div_self (theta_pos s hs).ne'

/-- **The sublattice reindexing**: the theta value at resolution `q`
is the Boltzmann mass of the sublattice `qℤ` — the analytic engine
of the event reading. -/
theorem theta_sq_eq_tsum_dvd (s : ℝ) {q : ℕ} (hq : q ≠ 0) :
    theta ((q : ℝ) ^ 2 * s)
      = ∑' j : {j : ℤ // (q : ℤ) ∣ j}, Real.exp (-s * (j : ℝ) ^ 2) := by
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq
  let e : ℤ ≃ {j : ℤ // (q : ℤ) ∣ j} :=
    { toFun := fun k => ⟨(q : ℤ) * k, ⟨k, rfl⟩⟩
      invFun := fun j => j.1 / (q : ℤ)
      left_inv := fun k => by
        simp [Int.mul_ediv_cancel_left _ hq0]
      right_inv := fun j => by
        obtain ⟨j, m, rfl⟩ := j
        exact Subtype.ext (by simp [Int.mul_ediv_cancel_left _ hq0]) }
  rw [← Equiv.tsum_eq e (fun j => Real.exp (-s * ((j : ℤ) : ℝ) ^ 2))]
  unfold theta
  refine tsum_congr fun k => ?_
  show Real.exp (-((q : ℝ) ^ 2 * s) * (k : ℝ) ^ 2)
    = Real.exp (-s * (((q : ℤ) * k : ℤ) : ℝ) ^ 2)
  congr 1
  push_cast
  ring

/-- **`resProb` is an honest event mass**: the relative Boltzmann
weight of the sublattice `qℤ` inside `ℤ` — the interpretation is a
theorem, not a gloss. -/
theorem resProb_eq_event_mass (s : ℝ) {q : ℕ} (hq : q ≠ 0) :
    resProb s q
      = (∑' j : {j : ℤ // (q : ℤ) ∣ j}, Real.exp (-s * (j : ℝ) ^ 2))
        / theta s := by
  rw [resProb, theta_sq_eq_tsum_dvd s hq]

/-- **The factorization identity**: `exp D` is the association ratio
of the divisibility events over `[gcd, lcm]` — the base mass `θ(s)`
cancels, and the defect compares the joint event against the product
of the marginals at the shared constraint. -/
theorem exp_defect_eq {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    Real.exp (defect s q q')
      = (resProb s q * resProb s q')
        / (resProb s (Nat.gcd q q') * resProb s (Nat.lcm q q')) := by
  have hg : Nat.gcd q q' ≠ 0 := fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hl : Nat.lcm q q' ≠ 0 := Nat.lcm_ne_zero hq hq'
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq'
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hg
  have hlR : (0 : ℝ) < (Nat.lcm q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hl
  have h1 : 0 < theta ((q : ℝ) ^ 2 * s) := theta_pos _ (by positivity)
  have h2 : 0 < theta ((q' : ℝ) ^ 2 * s) := theta_pos _ (by positivity)
  have h3 : 0 < theta ((Nat.gcd q q' : ℝ) ^ 2 * s) := theta_pos _ (by positivity)
  have h4 : 0 < theta ((Nat.lcm q q' : ℝ) ^ 2 * s) := theta_pos _ (by positivity)
  have hθs : 0 < theta s := theta_pos s hs
  unfold defect resProb
  rw [Real.exp_sub, Real.exp_add, Real.exp_add,
    Real.exp_log h1, Real.exp_log h2, Real.exp_log h3, Real.exp_log h4]
  field_simp

/-- **The defect is the log association ratio** — the precise sense
in which the defect measures the failure of the Gibbs measure to
factor over CRT. -/
theorem defect_eq_log_ratio {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    defect s q q'
      = Real.log ((resProb s q * resProb s q')
          / (resProb s (Nat.gcd q q') * resProb s (Nat.lcm q q'))) := by
  rw [← exp_defect_eq hs hq hq', Real.log_exp]

/-- **The conditional association identity**: minus the defect is
the log of the standard conditional association ratio — the joint
event against the product of the marginals, all conditioned on the
shared constraint `gcd ∣ X`. Positive association (ratio `> 1`) is
exactly the negative sign of the defect. -/
theorem neg_defect_eq_log_assoc {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    -defect s q q'
      = Real.log ((resProb s (Nat.lcm q q') / resProb s (Nat.gcd q q'))
          / ((resProb s q / resProb s (Nat.gcd q q'))
            * (resProb s q' / resProb s (Nat.gcd q q')))) := by
  have hg : Nat.gcd q q' ≠ 0 := fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hl : Nat.lcm q q' ≠ 0 := Nat.lcm_ne_zero hq hq'
  have hPq : (0 : ℝ) < resProb s q := resProb_pos hs hq
  have hPq' : (0 : ℝ) < resProb s q' := resProb_pos hs hq'
  have hPg : (0 : ℝ) < resProb s (Nat.gcd q q') := resProb_pos hs hg
  have hPl : (0 : ℝ) < resProb s (Nat.lcm q q') := resProb_pos hs hl
  rw [defect_eq_log_ratio hs hq hq', ← Real.log_inv]
  congr 1
  field_simp

/-- **Conditional positive association** (the sign theorem, read as
correlation): conditioned on the shared constraint `gcd ∣ X`, the
two divisibility events of an incomparable pair are strictly
positively associated — the joint conditional mass strictly exceeds
the product of the conditional marginals. -/
theorem condProb_mul_lt_of_incomparable {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    (resProb s q / resProb s (Nat.gcd q q'))
        * (resProb s q' / resProb s (Nat.gcd q q'))
      < resProb s (Nat.lcm q q') / resProb s (Nat.gcd q q') := by
  have hq : q ≠ 0 := fun h => hq'q (by rw [h]; exact dvd_zero q')
  have hq' : q' ≠ 0 := fun h => hqq' (by rw [h]; exact dvd_zero q)
  have hg : Nat.gcd q q' ≠ 0 := fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hl : Nat.lcm q q' ≠ 0 := Nat.lcm_ne_zero hq hq'
  have hPq : 0 < resProb s q := resProb_pos hs hq
  have hPq' : 0 < resProb s q' := resProb_pos hs hq'
  have hPg : 0 < resProb s (Nat.gcd q q') := resProb_pos hs hg
  have hPl : 0 < resProb s (Nat.lcm q q') := resProb_pos hs hl
  have hexp : Real.exp (defect s q q') < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (defect_neg_of_incomparable hs hqq' hq'q)
  rw [exp_defect_eq hs hq hq', div_lt_one (by positivity)] at hexp
  rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) hPg]
  nlinarith

/-- **Positive correlation of coprime divisibility events**: for
coprime resolutions `2 ≤ a, b` the Gibbs measure strictly favors
their joint occurrence — the unconditional face of the sign. -/
theorem resProb_mul_lt_of_coprime {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hco : Nat.Coprime a b) :
    resProb s a * resProb s b < resProb s (a * b) := by
  have hab : ¬a ∣ b := fun h => by
    have h1 : a = 1 := Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd dvd_rfl h)
    omega
  have hba : ¬b ∣ a := fun h => by
    have h1 : b = 1 := Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd h dvd_rfl)
    omega
  have h := condProb_mul_lt_of_incomparable hs hab hba
  have hgcd : Nat.gcd a b = 1 := hco
  rw [hgcd, Nat.Coprime.lcm_eq_mul hco, resProb_one hs] at h
  simpa using h

/-- **The association vanishes exactly on chains**: the joint mass
factors against the `[gcd, lcm]` interval iff the resolutions are
comparable — divisibility detection, in event language. -/
theorem resProb_mul_eq_iff {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) :
    resProb s q * resProb s q'
        = resProb s (Nat.gcd q q') * resProb s (Nat.lcm q q')
      ↔ q ∣ q' ∨ q' ∣ q := by
  have hg : Nat.gcd q q' ≠ 0 := fun h0 => hq (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hl : Nat.lcm q q' ≠ 0 := Nat.lcm_ne_zero hq hq'
  have hPg : 0 < resProb s (Nat.gcd q q') := resProb_pos hs hg
  have hPl : 0 < resProb s (Nat.lcm q q') := resProb_pos hs hl
  rw [← defect_eq_zero_iff hs (q := q) (q' := q')]
  constructor
  · intro heq
    have hone : Real.exp (defect s q q') = 1 := by
      rw [exp_defect_eq hs hq hq', heq, div_self (by positivity)]
    have hlog := congrArg Real.log hone
    rwa [Real.log_exp, Real.log_one] at hlog
  · intro h0
    have h := exp_defect_eq hs hq hq'
    rw [h0, Real.exp_zero, eq_comm, div_eq_one_iff_eq (by positivity)] at h
    exact h

end Theaetetus
