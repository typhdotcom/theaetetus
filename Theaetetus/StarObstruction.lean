import Theaetetus.Flattening

/-! # The star obstruction: no uniform deficit-PSD threshold

The saturation deficit `B = log θ(s)·J − M` has diagonal
`log θ(s)` and
off-diagonal entries `F(p) + F(q) − F(pq)`, `F(m) = log θ(m²s)`.
Fix the scale and let the satellites of `P = {2, q₁, …, qₙ}` grow:
the `2`-row entries saturate at `b = log θ(4s)` while the
satellite–satellite entries vanish — the deficit approaches a
star matrix whose smallest eigenvalue is `a − √n·b`,
`a = log θ(s)`. For `n > (a/b)²` the star is indefinite, so at
**every** scale some finite prime set has non-PSD deficit
(`deficit_not_psd`): `sup_P s_PSD(P) = ∞`, and no uniform PSD
threshold exists. Combined with the large-scale chamber theorem
(`pairing_cnd_large`), the converse `CND ⇒ deficit-PSD` fails at
every scale `s ≥ 1`, not merely at the numerical `s = 0.12`
witness (`cnd_not_psd`).

The proof needs no eigenvalue machinery: the explicit zero-free
weight `c(2) = n·b`, `c(qᵢ) = −a` already has negative energy
once the saturation errors are below `ε = b²/(4(a+b))`, which the
geometric tail bound (`theta_le`) supplies beyond an explicit
threshold. A counterexample kept as a theorem, in the
`SmallScale` witness style. -/

namespace Theaetetus

/-- **The saturation deficit kernel**: `B = log θ(s)·J − M`,
entrywise — the base complexity minus the pairing. On the
diagonal this is `log θ(s)`; off it, for coprime entries,
`F(p) + F(q) − F(pq)`. -/
noncomputable def deficit (s : ℝ) (p q : ℕ) : ℝ :=
  Real.log (theta s) - pairing s p q

@[simp] theorem deficit_self (s : ℝ) (p : ℕ) :
    deficit s p p = Real.log (theta s) := by
  unfold deficit
  rw [pairing_self]
  ring

/-- The exact off-diagonal entries on coprime pairs:
`F(p) + F(q) − F(pq)`. -/
theorem deficit_coprime {s : ℝ} {p q : ℕ} (hco : Nat.Coprime p q) :
    deficit s p q
      = Real.log (theta ((p : ℝ) ^ 2 * s))
        + Real.log (theta ((q : ℝ) ^ 2 * s))
        - Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) := by
  unfold deficit pairing
  rw [defect_coprime hco]
  ring

/-- **The zero-sum identity for the deficit**: against zero-sum
weights the deficit's quadratic form is the negated pairing form,
`cᵀBc = −cᵀMc` — the base term dies against the constraint. -/
theorem quadFormOn_deficit_eq_neg {s : ℝ} {P : Finset ℕ} {c : ℕ → ℝ}
    (hc : (∑ p ∈ P, c p) = 0) :
    quadFormOn (deficit s) P c = -quadFormOn (pairing s) P c := by
  unfold quadFormOn
  have hstep : ∀ p ∈ P, ∀ q ∈ P,
      c p * c q * deficit s p q
        = c p * (c q * Real.log (theta s))
          - c p * c q * pairing s p q := by
    intro p _ q _
    unfold deficit
    ring
  rw [Finset.sum_congr rfl
    (fun p hp => Finset.sum_congr rfl fun q hq => hstep p hp q hq)]
  have hinner : ∀ p ∈ P,
      (∑ q ∈ P, (c p * (c q * Real.log (theta s))
        - c p * c q * pairing s p q))
        = (∑ q ∈ P, c p * (c q * Real.log (theta s)))
          - ∑ q ∈ P, c p * c q * pairing s p q :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  have hB : ∀ p ∈ P,
      (∑ q ∈ P, c p * (c q * Real.log (theta s))) = 0 := by
    intro p _
    rw [← Finset.mul_sum, ← Finset.sum_mul, hc, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib,
    Finset.sum_congr rfl hB, Finset.sum_const_zero, zero_sub]

/-- **Deficit-PSD implies CND**, outright: one direction of the
chamber coupling. The converse fails at every scale `s ≥ 1`
(`cnd_not_psd`). -/
theorem deficit_psd_implies_cnd {s : ℝ} {P : Finset ℕ}
    (h : IsPSDOn (deficit s) P) : IsCNDOn (pairing s) P := by
  intro c hc
  have h1 := h c
  rw [quadFormOn_deficit_eq_neg hc] at h1
  linarith

/-- **Saturation with an explicit threshold**: beyond some `M ≥ 3`
every tail complexity `log θ(m²s)` is below `ε` — the log is at
most `θ − 1`, the geometric tail bound crushes `θ − 1`, and the
exponential does the rest. -/
private theorem exists_log_theta_small {s : ℝ} (hs : 0 < s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℕ, 3 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      Real.log (theta ((m : ℝ) ^ 2 * s)) ≤ ε := by
  obtain ⟨M, hM⟩ :=
    exists_nat_gt (max 3 (max (1 / s) (Real.log (4 / ε) / s)))
  have hM3 : (3 : ℝ) < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
  refine ⟨M, by exact_mod_cast hM3.le, ?_⟩
  intro m hm
  have hMm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by linarith
  have hmsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h1s : 1 / s < (m : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 3 _))
      (lt_of_lt_of_le hM hMm)
  have hlogs : Real.log (4 / ε) / s < (m : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 3 _))
      (lt_of_lt_of_le hM hMm)
  have hα1 : 1 ≤ (m : ℝ) ^ 2 * s := by
    have h1 : 1 < (m : ℝ) * s := (div_lt_iff₀ hs).mp h1s
    nlinarith [mul_le_mul_of_nonneg_right hmsq hs.le]
  have hαlog : Real.log (4 / ε) ≤ (m : ℝ) ^ 2 * s := by
    have h1 : Real.log (4 / ε) < (m : ℝ) * s := (div_lt_iff₀ hs).mp hlogs
    nlinarith [mul_le_mul_of_nonneg_right hmsq hs.le]
  have hα0 : (0 : ℝ) < (m : ℝ) ^ 2 * s := by nlinarith
  have hlog : Real.log (theta ((m : ℝ) ^ 2 * s))
      ≤ theta ((m : ℝ) ^ 2 * s) - 1 :=
    Real.log_le_sub_one_of_pos (theta_pos _ hα0)
  have hup := theta_le ((m : ℝ) ^ 2 * s) hα0
  have hehalf : Real.exp (-((m : ℝ) ^ 2 * s)) ≤ 1 / 2 := by
    have h1 : Real.exp (-((m : ℝ) ^ 2 * s)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h3 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hquot : Real.exp (-((m : ℝ) ^ 2 * s))
        / (1 - Real.exp (-((m : ℝ) ^ 2 * s)))
      ≤ 2 * Real.exp (-((m : ℝ) ^ 2 * s)) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ)
      < 1 - Real.exp (-((m : ℝ) ^ 2 * s)))]
    nlinarith [Real.exp_pos (-((m : ℝ) ^ 2 * s))]
  have hexpsmall : Real.exp (-((m : ℝ) ^ 2 * s)) ≤ ε / 4 := by
    have h1 : Real.exp (-((m : ℝ) ^ 2 * s))
        ≤ Real.exp (-(Real.log (4 / ε))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log (4 / ε)) = ε / 4 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 4 / ε),
        inv_div]
    rw [h2] at h1
    exact h1
  linarith

/-- Arbitrarily many primes above any threshold, as a `Finset`. -/
private theorem exists_primes_card_ge (n M : ℕ) :
    ∃ Q : Finset ℕ, Q.card = n ∧ ∀ q ∈ Q, Nat.Prime q ∧ M ≤ q := by
  induction n with
  | zero => exact ⟨∅, rfl, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | succ k ih =>
    obtain ⟨Q, hcard, hmem⟩ := ih
    obtain ⟨p, hple, hp⟩ :=
      Nat.exists_infinite_primes (max M (Q.sup id + 1))
    have hpQ : p ∉ Q := by
      intro hin
      have h1 : p ≤ Q.sup id := Finset.le_sup (f := id) hin
      have h2 : Q.sup id + 1 ≤ p := le_trans (le_max_right _ _) hple
      omega
    refine ⟨insert p Q, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hpQ, hcard]
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact ⟨hp, le_trans (le_max_left _ _) hple⟩
      · exact hmem q hq'

/-- **The star obstruction**: at every scale, some finite prime
set has non-PSD saturation deficit — `sup_P s_PSD(P) = ∞`, no
uniform deficit-PSD threshold exists. The witness is the star
weight `c(2) = n·log θ(4s)`, `c(qᵢ) = −log θ(s)` on one small
prime and `n` sufficiently large satellites. -/
theorem deficit_not_psd {s : ℝ} (hs : 0 < s) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p)
      ∧ ¬ IsPSDOn (deficit s) P := by
  have ha : 0 < Real.log (theta s) := Real.log_pos (theta_gt_one s hs)
  have hb : 0 < Real.log (theta (4 * s)) :=
    Real.log_pos (theta_gt_one _ (by linarith))
  have hab : (0 : ℝ)
      < Real.log (theta s) + Real.log (theta (4 * s)) := by linarith
  -- the tolerance, held only through its polynomial identity
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε
      ∧ 4 * ε * (Real.log (theta s) + Real.log (theta (4 * s)))
        = Real.log (theta (4 * s)) ^ 2 := by
    refine ⟨Real.log (theta (4 * s)) ^ 2
      / (4 * (Real.log (theta s) + Real.log (theta (4 * s)))),
      by positivity, ?_⟩
    field_simp
  -- the satellite count
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, 1 ≤ n
      ∧ 2 * Real.log (theta s) ^ 2
        < (n : ℝ) * Real.log (theta (4 * s)) ^ 2 := by
    refine ⟨⌈2 * Real.log (theta s) ^ 2
      / Real.log (theta (4 * s)) ^ 2⌉₊ + 1, by omega, ?_⟩
    have hx := Nat.le_ceil (2 * Real.log (theta s) ^ 2
      / Real.log (theta (4 * s)) ^ 2)
    have hcast : 2 * Real.log (theta s) ^ 2
          / Real.log (theta (4 * s)) ^ 2
        < ((⌈2 * Real.log (theta s) ^ 2
          / Real.log (theta (4 * s)) ^ 2⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hb2 : (0 : ℝ) < Real.log (theta (4 * s)) ^ 2 := by positivity
    calc 2 * Real.log (theta s) ^ 2
        = (2 * Real.log (theta s) ^ 2
            / Real.log (theta (4 * s)) ^ 2)
          * Real.log (theta (4 * s)) ^ 2 := by field_simp
      _ < _ := mul_lt_mul_of_pos_right hcast hb2
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  obtain ⟨M, hM3, hMsmall⟩ := exists_log_theta_small hs hεpos
  obtain ⟨Q, hQcard, hQmem⟩ := exists_primes_card_ge n M
  have hQ3 : ∀ q ∈ Q, 3 ≤ q :=
    fun q hq => le_trans hM3 (hQmem q hq).2
  have h2Q : (2 : ℕ) ∉ Q := by
    intro h
    have := hQ3 2 h
    omega
  refine ⟨insert 2 Q, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Nat.prime_two
    · exact (hQmem p hp').1
  -- the star weight
  intro hPSD
  set c : ℕ → ℝ := fun m =>
    if m = 2 then (n : ℝ) * Real.log (theta (4 * s))
    else -Real.log (theta s) with hc_def
  have hc2 : c 2 = (n : ℝ) * Real.log (theta (4 * s)) := if_pos rfl
  have hcQ : ∀ q ∈ Q, c q = -Real.log (theta s) := by
    intro q hq
    have := hQ3 q hq
    exact if_neg (by omega)
  -- entry bounds
  have hK2q : ∀ q ∈ Q, Real.log (theta (4 * s)) - ε ≤ deficit s 2 q := by
    intro q hq
    have hq3 := hQ3 q hq
    have hqM := (hQmem q hq).2
    have hco : Nat.Coprime 2 q :=
      (Nat.coprime_primes Nat.prime_two (hQmem q hq).1).mpr (by omega)
    rw [deficit_coprime hco,
      show ((2 : ℕ) : ℝ) ^ 2 * s = 4 * s by push_cast; ring,
      show (((2 : ℕ) : ℝ) * (q : ℝ)) ^ 2 * s
        = ((2 * q : ℕ) : ℝ) ^ 2 * s by push_cast; ring]
    have hFq : 0 ≤ Real.log (theta ((q : ℝ) ^ 2 * s)) := by
      have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
      exact Real.log_nonneg (theta_gt_one _ (by positivity)).le
    have hF2q := hMsmall (2 * q) (by omega)
    linarith
  have hKq2 : ∀ q ∈ Q, Real.log (theta (4 * s)) - ε ≤ deficit s q 2 := by
    intro q hq
    have hq3 := hQ3 q hq
    have hqM := (hQmem q hq).2
    have hco : Nat.Coprime q 2 :=
      (Nat.coprime_primes (hQmem q hq).1 Nat.prime_two).mpr (by omega)
    rw [deficit_coprime hco,
      show ((2 : ℕ) : ℝ) ^ 2 * s = 4 * s by push_cast; ring,
      show (((q : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) ^ 2 * s
        = ((q * 2 : ℕ) : ℝ) ^ 2 * s by push_cast; ring]
    have hFq : 0 ≤ Real.log (theta ((q : ℝ) ^ 2 * s)) := by
      have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
      exact Real.log_nonneg (theta_gt_one _ (by positivity)).le
    have hFq2 := hMsmall (q * 2) (by omega)
    linarith
  have hKpq : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → deficit s p q ≤ 2 * ε := by
    intro p hp q hq hne
    have hco : Nat.Coprime p q :=
      (Nat.coprime_primes (hQmem p hp).1 (hQmem q hq).1).mpr hne
    rw [deficit_coprime hco]
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (hQmem p hp).1.pos
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (hQmem q hq).1.pos
    have hFpq : 0 ≤ Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) :=
      Real.log_nonneg (theta_gt_one _ (by positivity)).le
    have h1 := hMsmall p (hQmem p hp).2
    have h2 := hMsmall q (hQmem q hq).2
    linarith
  -- expand the quadratic form over the insert
  have hrows : (∑ p ∈ Q, ∑ q ∈ insert 2 Q, c p * c q * deficit s p q)
      = ∑ p ∈ Q, (c p * c 2 * deficit s p 2
        + ∑ q ∈ Q, c p * c q * deficit s p q) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_insert h2Q
  have hexpand : quadFormOn (deficit s) (insert 2 Q) c
      = c 2 * c 2 * deficit s 2 2
        + (∑ q ∈ Q, c 2 * c q * deficit s 2 q)
        + ((∑ p ∈ Q, c p * c 2 * deficit s p 2)
        + ∑ p ∈ Q, ∑ q ∈ Q, c p * c q * deficit s p q) := by
    unfold quadFormOn
    rw [Finset.sum_insert h2Q, Finset.sum_insert h2Q, hrows,
      Finset.sum_add_distrib, ← add_assoc]
  -- the four pieces, bounded
  have hA : c 2 * c 2 * deficit s 2 2
      = ((n : ℝ) * Real.log (theta (4 * s)))
        * ((n : ℝ) * Real.log (theta (4 * s))) * Real.log (theta s) := by
    rw [hc2, deficit_self]
  have hNBL : (0 : ℝ) ≤ (n : ℝ) * Real.log (theta (4 * s))
      * Real.log (theta s) :=
    le_of_lt (mul_pos (mul_pos hN hb) ha)
  have hB2 : (∑ q ∈ Q, c 2 * c q * deficit s 2 q)
      ≤ (n : ℝ) * (-((n : ℝ) * Real.log (theta (4 * s))
        * Real.log (theta s) * (Real.log (theta (4 * s)) - ε))) := by
    calc (∑ q ∈ Q, c 2 * c q * deficit s 2 q)
        ≤ Q.card • (-((n : ℝ) * Real.log (theta (4 * s))
            * Real.log (theta s) * (Real.log (theta (4 * s)) - ε))) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
          rw [hc2, hcQ q hq]
          have hk := hK2q q hq
          nlinarith [mul_le_mul_of_nonneg_left hk hNBL]
      _ = _ := by rw [hQcard, nsmul_eq_mul]
  have hC2 : (∑ p ∈ Q, c p * c 2 * deficit s p 2)
      ≤ (n : ℝ) * (-((n : ℝ) * Real.log (theta (4 * s))
        * Real.log (theta s) * (Real.log (theta (4 * s)) - ε))) := by
    calc (∑ p ∈ Q, c p * c 2 * deficit s p 2)
        ≤ Q.card • (-((n : ℝ) * Real.log (theta (4 * s))
            * Real.log (theta s) * (Real.log (theta (4 * s)) - ε))) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
          rw [hc2, hcQ p hp]
          have hk := hKq2 p hp
          nlinarith [mul_le_mul_of_nonneg_left hk hNBL]
      _ = _ := by rw [hQcard, nsmul_eq_mul]
  have hLL : (0 : ℝ) ≤ Real.log (theta s) * Real.log (theta s) :=
    mul_self_nonneg _
  have hD : (∑ p ∈ Q, ∑ q ∈ Q, c p * c q * deficit s p q)
      ≤ (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
          * Real.log (theta s)
        + (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
          * (2 * ε))) := by
    calc (∑ p ∈ Q, ∑ q ∈ Q, c p * c q * deficit s p q)
        ≤ Q.card • (Real.log (theta s) * Real.log (theta s)
            * Real.log (theta s)
          + (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
            * (2 * ε))) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
          have hsplit : (∑ q ∈ Q, c p * c q * deficit s p q)
              = c p * c p * deficit s p p
                + ∑ q ∈ Q.erase p, c p * c q * deficit s p q := by
            rw [← Finset.add_sum_erase Q _ hp]
          have hself : c p * c p * deficit s p p
              = Real.log (theta s) * Real.log (theta s)
                * Real.log (theta s) := by
            rw [hcQ p hp, deficit_self]
            ring
          have herase : (∑ q ∈ Q.erase p, c p * c q * deficit s p q)
              ≤ (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
                * (2 * ε)) := by
            calc (∑ q ∈ Q.erase p, c p * c q * deficit s p q)
                ≤ (Q.erase p).card • (Real.log (theta s)
                    * Real.log (theta s) * (2 * ε)) := by
                  refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
                  obtain ⟨hne, hqQ⟩ := Finset.mem_erase.mp hq
                  rw [hcQ p hp, hcQ q hqQ]
                  have hk := hKpq p hp q hqQ (Ne.symm hne)
                  nlinarith [mul_le_mul_of_nonneg_left hk hLL]
              _ ≤ (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
                  * (2 * ε)) := by
                  rw [Finset.card_erase_of_mem hp, hQcard, nsmul_eq_mul]
                  have hcast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
                    exact_mod_cast Nat.sub_le n 1
                  have hf : (0 : ℝ) ≤ Real.log (theta s)
                      * Real.log (theta s) * (2 * ε) := by
                    have := hεpos
                    nlinarith [hLL]
                  exact mul_le_mul_of_nonneg_right hcast hf
          rw [hsplit]
          linarith [hself, herase]
      _ = _ := by rw [hQcard, nsmul_eq_mul]
  -- the assembled bound is negative
  have h1N : (n : ℝ) ^ 2 * Real.log (theta s)
        * (4 * ε * (Real.log (theta s) + Real.log (theta (4 * s))))
      = (n : ℝ) ^ 2 * Real.log (theta s)
        * Real.log (theta (4 * s)) ^ 2 := by
    rw [hε]
  have h2N := mul_lt_mul_of_pos_left hn
    (half_pos (mul_pos hN ha))
  have hX : ((n : ℝ) * Real.log (theta (4 * s)))
        * ((n : ℝ) * Real.log (theta (4 * s))) * Real.log (theta s)
      + (n : ℝ) * (-((n : ℝ) * Real.log (theta (4 * s))
        * Real.log (theta s) * (Real.log (theta (4 * s)) - ε)))
      + ((n : ℝ) * (-((n : ℝ) * Real.log (theta (4 * s))
        * Real.log (theta s) * (Real.log (theta (4 * s)) - ε)))
      + (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
          * Real.log (theta s)
        + (n : ℝ) * (Real.log (theta s) * Real.log (theta s)
          * (2 * ε)))) < 0 := by
    nlinarith [h1N, h2N, ha, hb, hN, hεpos]
  have hcontra := hPSD c
  rw [hexpand] at hcontra
  nlinarith [hA, hB2, hC2, hD, hX, hcontra]

/-- **The converse fails at every large scale**: for every
`s ≥ 1` there is a finite prime set on which the pairing is CND
(`pairing_cnd_large` — every set is) while the saturation deficit
is not PSD. The CND and deficit-PSD conditions are separated at all
scales, not merely at the numerical `s = 0.12` witness. -/
theorem cnd_not_psd {s : ℝ} (hs : 1 ≤ s) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p)
      ∧ IsCNDOn (pairing s) P ∧ ¬ IsPSDOn (deficit s) P := by
  obtain ⟨P, hP, hnpsd⟩ := deficit_not_psd (lt_of_lt_of_le one_pos hs)
  exact ⟨P, hP, pairing_cnd_large hs hP, hnpsd⟩

end Theaetetus
