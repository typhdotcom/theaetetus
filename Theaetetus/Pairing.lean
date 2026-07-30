import Theaetetus.Submodular

/-! # The prime pairing ⟨p, p′⟩

**First theorems of the pairing.** For resolutions `p, p′` the **pairing** is
the negated defect `⟨p, p′⟩ := −D_s(p, p′)` — for distinct primes a
strictly positive two-point function on the primes, mediated by the
geometry of the carrier (`pairing_pos`, from the sign).

The asymptotics: for coprime `p, q ≥ 1` the pairing is squeezed by

    log θ(s) − (θ(p²s)−1) − (θ(q²s)−1) < ⟨p, q⟩ < log θ(s),

(`base_sub_lt_pairing`, `pairing_lt_base`) with corrections decaying
geometrically (`theta_sub_one_le_geo`), so along coprime pairs going
to infinity the pairing **saturates at the complexity of the base**:

    ⟨p, q⟩ → log θ(s)     (`tendsto_pairing`).

Far-apart primes couple at full base strength; the interesting
structure of the defect matrix is at bounded height. -/

namespace Theaetetus

open Filter Topology

/-- **The pairing** `⟨p, q⟩ := −D_s(p, q)` — the coupling strength
of two resolutions, positive where the defect is negative. -/
noncomputable def pairing (s : ℝ) (p q : ℕ) : ℝ := -defect s p q

/-- The pairing vanishes on the diagonal: a resolution does not
couple with itself. -/
@[simp] theorem pairing_self (s : ℝ) (p : ℕ) : pairing s p p = 0 := by
  unfold pairing
  rw [defect_self]
  exact neg_zero

/-- **Coprime evenness for the pairing** (the negated-defect form
of `defect_scale_even`): on a coprime pair the reflection fixes
the pair and moves only the scale, `s ↦ π²/(s·(pq)²)`. -/
theorem pairing_scale_even {s : ℝ} (hs : 0 < s) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hco : Nat.Coprime p q) :
    pairing s p q
      = pairing (Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s)) p q := by
  unfold pairing
  rw [defect_scale_even hs hp hq hco]

/-- The pairing is symmetric. -/
theorem pairing_comm (s : ℝ) (p q : ℕ) : pairing s p q = pairing s q p := by
  unfold pairing
  rw [defect_comm]

/-- **Positivity on the primes** (via the sign): distinct primes are
incomparable in the divisibility lattice, so their pairing is
strictly positive at every scale. -/
theorem pairing_pos {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : 0 < pairing s p q := by
  have h1 : ¬p ∣ q := fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have h2 : ¬q ∣ p := fun hdvd =>
    hne (((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd).symm)
  have := defect_neg_of_incomparable hs h1 h2
  unfold pairing
  linarith

/-- The defect at a coprime pair in closed form: `gcd = 1`,
`lcm = p·q`. -/
theorem defect_coprime {s : ℝ} {p q : ℕ} (hco : Nat.Coprime p q) :
    defect s p q
      = (Real.log (theta ((p : ℝ) ^ 2 * s)) + Real.log (theta ((q : ℝ) ^ 2 * s)))
        - (Real.log (theta s)
          + Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))) := by
  unfold defect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco,
    show ((1 : ℕ) : ℝ) ^ 2 * s = s from by norm_num,
    show ((p * q : ℕ) : ℝ) ^ 2 * s = ((p : ℝ) * (q : ℝ)) ^ 2 * s from by
      push_cast; ring]

/-- **The ceiling**: the pairing of a coprime pair is strictly below
the complexity of the base, `⟨p, q⟩ < log θ(s)` — the coupling of
two resolutions can never exceed what the unresolved carrier
holds. -/
theorem pairing_lt_base {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hco : Nat.Coprime p q) : pairing s p q < Real.log (theta s) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hanti : theta (((p : ℝ) * (q : ℝ)) ^ 2 * s) ≤ theta ((p : ℝ) ^ 2 * s) := by
    apply theta_anti (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (p : ℝ))
      (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1))
      (by linarith : (0 : ℝ) ≤ (q : ℝ) + 1)) hs.le]
  have hlog1 : Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ Real.log (theta ((p : ℝ) ^ 2 * s)) :=
    Real.log_le_log (theta_pos _ (by positivity)) hanti
  have hlog2 : 0 < Real.log (theta ((q : ℝ) ^ 2 * s)) :=
    Real.log_pos (theta_gt_one _ (by positivity))
  unfold pairing
  rw [defect_coprime hco]
  linarith

/-- **The floor**: the pairing sits above the base complexity minus
the (small) excesses of the two resolved theta values. -/
theorem base_sub_lt_pairing {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hco : Nat.Coprime p q) :
    Real.log (theta s)
        - ((theta ((p : ℝ) ^ 2 * s) - 1) + (theta ((q : ℝ) ^ 2 * s) - 1))
      < pairing s p q := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have h1 : Real.log (theta ((p : ℝ) ^ 2 * s)) ≤ theta ((p : ℝ) ^ 2 * s) - 1 :=
    Real.log_le_sub_one_of_pos (theta_pos _ (by positivity))
  have h2 : Real.log (theta ((q : ℝ) ^ 2 * s)) ≤ theta ((q : ℝ) ^ 2 * s) - 1 :=
    Real.log_le_sub_one_of_pos (theta_pos _ (by positivity))
  have h3 : 0 < Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) :=
    Real.log_pos (theta_gt_one _ (by positivity))
  unfold pairing
  rw [defect_coprime hco]
  linarith

/-- The excess of a resolved theta value decays geometrically in the
resolution: `θ(p²s) − 1 ≤ 2·(e^{−s})^p/(1 − e^{−s})`. -/
theorem theta_sub_one_le_geo {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : 1 ≤ p) :
    theta ((p : ℝ) ^ 2 * s) - 1
      ≤ 2 * (Real.exp (-s) ^ p / (1 - Real.exp (-s))) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hα : (0 : ℝ) < (p : ℝ) ^ 2 * s := by positivity
  have hle := theta_le _ hα
  have hc0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hc1 : Real.exp (-s) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hmono : Real.exp (-((p : ℝ) ^ 2 * s)) ≤ Real.exp (-s) ^ p := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg hp0.le
      (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)) hs.le]
  have hless : Real.exp (-((p : ℝ) ^ 2 * s)) ≤ Real.exp (-s) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (p : ℝ) + 1)) hs.le]
  have hden1 : (0 : ℝ) < 1 - Real.exp (-s) := by linarith
  have hden2 : (0 : ℝ) < 1 - Real.exp (-((p : ℝ) ^ 2 * s)) := by linarith
  have hfrac : Real.exp (-((p : ℝ) ^ 2 * s)) / (1 - Real.exp (-((p : ℝ) ^ 2 * s)))
      ≤ Real.exp (-s) ^ p / (1 - Real.exp (-s)) := by
    rw [div_le_div_iff₀ hden2 hden1]
    have hstep1 : Real.exp (-((p : ℝ) ^ 2 * s)) * (1 - Real.exp (-s))
        ≤ Real.exp (-s) ^ p * (1 - Real.exp (-s)) :=
      mul_le_mul_of_nonneg_right hmono hden1.le
    have hstep2 : Real.exp (-s) ^ p * (1 - Real.exp (-s))
        ≤ Real.exp (-s) ^ p * (1 - Real.exp (-((p : ℝ) ^ 2 * s))) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hc0.le p)
    linarith
  linarith

/-- **SATURATION AT THE BASE** (the first asymptotic): along
coprime pairs going to infinity, the pairing converges to the
complexity of the unresolved carrier —
`⟨p, q⟩ → log θ(s)` as `min(p,q) → ∞`. -/
theorem tendsto_pairing {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ × ℕ => pairing s n.1 n.2)
      (atTop ⊓ 𝓟 {n : ℕ × ℕ | Nat.Coprime n.1 n.2})
      (𝓝 (Real.log (theta s))) := by
  have hc0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hc1 : Real.exp (-s) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  set F := atTop ⊓ 𝓟 {n : ℕ × ℕ | Nat.Coprime n.1 n.2} with hF
  have hpow : Tendsto (fun k : ℕ => Real.exp (-s) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1
  have hfst : Tendsto (fun n : ℕ × ℕ => Real.exp (-s) ^ n.1) F (𝓝 0) := by
    refine hpow.comp (Tendsto.mono_left ?_ inf_le_left)
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun n : ℕ × ℕ => Real.exp (-s) ^ n.2) F (𝓝 0) := by
    refine hpow.comp (Tendsto.mono_left ?_ inf_le_left)
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hlim : Tendsto (fun n : ℕ × ℕ =>
      Real.log (theta s) - (2 / (1 - Real.exp (-s)) * Real.exp (-s) ^ n.1
        + 2 / (1 - Real.exp (-s)) * Real.exp (-s) ^ n.2)) F
      (𝓝 (Real.log (theta s))) := by
    have h := ((hfst.const_mul (2 / (1 - Real.exp (-s)))).add
      (hsnd.const_mul (2 / (1 - Real.exp (-s))))).const_sub (Real.log (theta s))
    simpa using h
  have hev : ∀ᶠ n : ℕ × ℕ in F, (1 ≤ n.1 ∧ 1 ≤ n.2) ∧ Nat.Coprime n.1 n.2 := by
    rw [hF, eventually_inf_principal]
    filter_upwards [eventually_ge_atTop ((1 : ℕ), (1 : ℕ))] with n hn hmem
    exact ⟨⟨hn.1, hn.2⟩, hmem⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with n hn
    obtain ⟨⟨hp1, hq1⟩, hco⟩ := hn
    have hb := base_sub_lt_pairing hs hp1 hq1 hco
    have h1 := theta_sub_one_le_geo hs hp1
    have h2 := theta_sub_one_le_geo hs hq1
    have hrw1 : 2 / (1 - Real.exp (-s)) * Real.exp (-s) ^ n.1
        = 2 * (Real.exp (-s) ^ n.1 / (1 - Real.exp (-s))) := by ring
    have hrw2 : 2 / (1 - Real.exp (-s)) * Real.exp (-s) ^ n.2
        = 2 * (Real.exp (-s) ^ n.2 / (1 - Real.exp (-s))) := by ring
    linarith
  · filter_upwards [hev] with n hn
    obtain ⟨⟨hp1, hq1⟩, hco⟩ := hn
    exact (pairing_lt_base hs hp1 hq1 hco).le

end Theaetetus
