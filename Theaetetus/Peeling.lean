import Theaetetus.PartitionTower

/-! # Spectral peeling: the least energy and its multiplicity

The first extraction step of the inverse problem. On a nontrivial
partition tower, summability forces the energy spectrum to be
locally finite (`finite_energy_le`), so the least positive energy
is attained (`leastEnergy_isLeast`) with finite multiplicity. Both
are then read off the partition function asymptotically:

    e^{β·λ₁} · (Z(β) − 1)  →  N₁          (`tendsto_exp_mul_Z_sub_one`)
    −log(Z(β) − 1) / β     →  λ₁          (`tendsto_neg_log_Z_sub_one_div`)

— the second is a corollary of the first through the logarithm,
no squeeze required. Sampled along `β = m²` these consume exactly
the data the recovery formula produces
(`tendsto_defect_row_sub_succ`): one fixed defect matrix
determines `λ₁` and `N₁`. Subtracting the recovered layer and
recursing is the remaining step of the peeling program. -/

namespace Theaetetus

namespace PartitionTower

universe u

open Filter Topology

variable (T : PartitionTower.{u})

/-- The least positive energy of the tower: the infimum of the
nonmodal spectrum (junk value on a trivial tower). -/
noncomputable def leastEnergy : ℝ :=
  sInf (T.E '' {k | k ≠ T.modal})

/-- **Local finiteness of the spectrum**: only finitely many
sectors sit below any energy threshold — an infinite family of
Boltzmann weights bounded below would break summability. -/
theorem finite_energy_le (c : ℝ) :
    {k : T.Λ | k ≠ T.modal ∧ T.E k ≤ c}.Finite := by
  have hev : ∀ᶠ k in Filter.cofinite,
      Real.exp (-T.E k) < Real.exp (-c) :=
    T.summable.tendsto_cofinite_zero.eventually_lt_const
      (Real.exp_pos (-c))
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq, not_lt]
  exact Real.exp_le_exp.mpr (by linarith [hk.2])

/-- The level set of the least energy. -/
theorem finite_level :
    {k : T.Λ | k ≠ T.modal ∧ T.E k = T.leastEnergy}.Finite :=
  (T.finite_energy_le T.leastEnergy).subset fun _ hk => ⟨hk.1, hk.2.le⟩

/-- **The multiplicity of the least energy**: the size of its
level set. -/
noncomputable def leastEnergyMult : ℕ :=
  T.finite_level.toFinset.card

/-- On a nontrivial tower the least positive energy is attained:
the infimum is a member of the nonmodal spectrum and a lower bound
for it. -/
theorem leastEnergy_isLeast (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    IsLeast (T.E '' {k | k ≠ T.modal}) T.leastEnergy := by
  classical
  obtain ⟨w, hw⟩ := hnt
  have hfin := T.finite_energy_le (T.E w)
  have hwmem : w ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hw, le_rfl⟩
  obtain ⟨k₀, hk₀, hmin⟩ :=
    hfin.toFinset.exists_min_image T.E ⟨w, hwmem⟩
  rw [Set.Finite.mem_toFinset] at hk₀
  have hlb : ∀ x ∈ T.E '' {k | k ≠ T.modal}, T.E k₀ ≤ x := by
    rintro x ⟨k, hk, rfl⟩
    by_cases hle : T.E k ≤ T.E w
    · exact hmin k (by rw [Set.Finite.mem_toFinset]; exact ⟨hk, hle⟩)
    · have h1 : T.E k₀ ≤ T.E w := hmin w hwmem
      linarith [not_le.mp hle]
  have hIs : IsLeast (T.E '' {k | k ≠ T.modal}) (T.E k₀) :=
    ⟨⟨k₀, hk₀.1, rfl⟩, hlb⟩
  have heq : T.leastEnergy = T.E k₀ := by
    unfold leastEnergy
    exact hIs.csInf_eq
  rw [heq]
  exact hIs

/-- The least energy is a lower bound off the modal sector. -/
theorem leastEnergy_le (hnt : ∃ k : T.Λ, k ≠ T.modal) {k : T.Λ}
    (hk : k ≠ T.modal) : T.leastEnergy ≤ T.E k :=
  (T.leastEnergy_isLeast hnt).2 ⟨k, hk, rfl⟩

/-- The least energy is strictly positive. -/
theorem leastEnergy_pos (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    0 < T.leastEnergy := by
  obtain ⟨⟨k₀, hk₀, hEk₀⟩, -⟩ := T.leastEnergy_isLeast hnt
  rw [← hEk₀]
  exact T.E_pos k₀ hk₀

/-- The multiplicity is positive on a nontrivial tower. -/
theorem leastEnergyMult_pos (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    0 < T.leastEnergyMult := by
  obtain ⟨⟨k₀, hk₀, hEk₀⟩, -⟩ := T.leastEnergy_isLeast hnt
  rw [leastEnergyMult, Finset.card_pos]
  exact ⟨k₀, by rw [Set.Finite.mem_toFinset]; exact ⟨hk₀, hEk₀⟩⟩

/-- **The multiplicity limit**: rescaled by the least energy, the
excess of the partition function counts the bottom level —
Tannery on the spectrum shifted by `λ₁`, whose level set plays
the modal role. -/
theorem tendsto_exp_mul_Z_sub_one (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun β : ℝ => Real.exp (β * T.leastEnergy) * (T.Z β - 1))
      atTop (𝓝 (T.leastEnergyMult : ℝ)) := by
  classical
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (β : ℝ) (k : T.Λ) =>
      if k = T.modal then 0
      else Real.exp (-(β * (T.E k - T.leastEnergy))))
    (g := fun k : T.Λ =>
      if k ≠ T.modal ∧ T.E k = T.leastEnergy then (1 : ℝ) else 0)
    (bound := fun k => Real.exp T.leastEnergy * Real.exp (-T.E k))
    (T.summable.mul_left _)
    (by
      intro k
      by_cases hk : k = T.modal
      · subst hk
        have hfv : ∀ β : ℝ, (if T.modal = T.modal then (0 : ℝ)
            else Real.exp (-(β * (T.E T.modal - T.leastEnergy)))) = 0 :=
          fun _ => if_pos rfl
        have hgv : (if T.modal ≠ T.modal ∧ T.E T.modal = T.leastEnergy
            then (1 : ℝ) else 0) = 0 := if_neg fun h => h.1 rfl
        rw [hgv]
        exact tendsto_const_nhds.congr fun β => (hfv β).symm
      · by_cases hE : T.E k = T.leastEnergy
        · have hfv : ∀ β : ℝ, (if k = T.modal then (0 : ℝ)
              else Real.exp (-(β * (T.E k - T.leastEnergy)))) = 1 := by
            intro β
            rw [if_neg hk, hE, sub_self, mul_zero, neg_zero, Real.exp_zero]
          have hgv : (if k ≠ T.modal ∧ T.E k = T.leastEnergy
              then (1 : ℝ) else 0) = 1 := if_pos ⟨hk, hE⟩
          simp only [hfv, hgv]
          exact tendsto_const_nhds
        · have hfv : ∀ β : ℝ, (if k = T.modal then (0 : ℝ)
              else Real.exp (-(β * (T.E k - T.leastEnergy))))
              = Real.exp (-(β * (T.E k - T.leastEnergy))) :=
            fun _ => if_neg hk
          have hgv : (if k ≠ T.modal ∧ T.E k = T.leastEnergy
              then (1 : ℝ) else 0) = 0 := if_neg fun h => hE h.2
          simp only [hfv, hgv]
          have hpos : 0 < T.E k - T.leastEnergy := by
            have := T.leastEnergy_le hnt hk
            cases lt_or_eq_of_le this with
            | inl h => linarith
            | inr h => exact absurd h.symm hE
          have h1 : Tendsto (fun β : ℝ => β * (T.E k - T.leastEnergy))
              atTop atTop :=
            (tendsto_mul_const_atTop_of_pos hpos).mpr tendsto_id
          have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
          simpa only [Function.comp_def] using h2)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      intro k
      by_cases hk : k = T.modal
      · simp only [if_pos hk, norm_zero]
        positivity
      · simp only [if_neg hk, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        have hE : 0 ≤ T.E k - T.leastEnergy := by
          linarith [T.leastEnergy_le hnt hk]
        calc Real.exp (-(β * (T.E k - T.leastEnergy)))
            ≤ Real.exp (-(1 * (T.E k - T.leastEnergy))) :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = Real.exp T.leastEnergy * Real.exp (-T.E k) := by
              rw [← Real.exp_add]
              congr 1
              ring)
  have hg : (∑' k : T.Λ,
      (if k ≠ T.modal ∧ T.E k = T.leastEnergy then (1 : ℝ) else 0))
      = (T.leastEnergyMult : ℝ) := by
    have h0 : ∀ k ∉ T.finite_level.toFinset,
        (if k ≠ T.modal ∧ T.E k = T.leastEnergy then (1 : ℝ) else 0)
          = 0 := by
      intro k hk
      refine if_neg fun hpred => hk ?_
      rw [Set.Finite.mem_toFinset]
      exact hpred
    rw [tsum_eq_sum h0]
    rw [Finset.sum_congr rfl
      (fun k hk => if_pos
        (show k ≠ T.modal ∧ T.E k = T.leastEnergy from
          T.finite_level.mem_toFinset.mp hk)),
      Finset.sum_const, nsmul_eq_mul, mul_one, leastEnergyMult]
  rw [hg] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  have hsum := T.summable_Z hβ
  have hsplit : T.Z β
      = 1 + ∑' k : T.Λ,
          (if k = T.modal then 0 else Real.exp (-(β * T.E k))) := by
    unfold Z
    rw [hsum.tsum_eq_add_tsum_ite T.modal]
    congr 1
    rw [T.E_modal, mul_zero, neg_zero, Real.exp_zero]
  rw [hsplit, show (1 : ℝ)
      + (∑' k : T.Λ, (if k = T.modal then 0
          else Real.exp (-(β * T.E k)))) - 1
      = ∑' k : T.Λ, (if k = T.modal then 0
          else Real.exp (-(β * T.E k))) from by ring,
    ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = T.modal
  · simp [hk]
  · simp only [if_neg hk]
    rw [← Real.exp_add]
    congr 1
    ring

/-- **The least-energy limit**: through the logarithm of the
multiplicity limit — the observable `−log(Z(β) − 1)/β` recovers
`λ₁`. -/
theorem tendsto_neg_log_Z_sub_one_div (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun β : ℝ => -Real.log (T.Z β - 1) / β)
      atTop (𝓝 T.leastEnergy) := by
  have hB := T.tendsto_exp_mul_Z_sub_one hnt
  have hN : (0 : ℝ) < (T.leastEnergyMult : ℝ) := by
    exact_mod_cast T.leastEnergyMult_pos hnt
  have hev : ∀ᶠ β : ℝ in atTop, 0 < T.Z β - 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    linarith [T.one_lt_Z hβ hnt]
  have hlog := (Real.continuousAt_log (ne_of_gt hN)).tendsto.comp hB
  have hdiv := hlog.div_atTop tendsto_id
  have halg : ∀ᶠ β : ℝ in atTop,
      T.leastEnergy
        - Real.log (Real.exp (β * T.leastEnergy) * (T.Z β - 1)) / β
      = -Real.log (T.Z β - 1) / β := by
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β hZ hβ0
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
    field_simp
    ring
  have hfinal := (tendsto_const_nhds (x := T.leastEnergy)).sub hdiv
  rw [sub_zero] at hfinal
  exact hfinal.congr' halg

/-- The least-energy limit along the recovery samples `β = m²`. -/
theorem tendsto_leastEnergy_sample (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun m : ℕ =>
        -Real.log (T.Z ((m : ℝ) ^ 2) - 1) / (m : ℝ) ^ 2)
      atTop (𝓝 T.leastEnergy) :=
  (T.tendsto_neg_log_Z_sub_one_div hnt).comp
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)

/-- The multiplicity limit along the recovery samples `β = m²`. -/
theorem tendsto_leastEnergyMult_sample (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun m : ℕ =>
        Real.exp ((m : ℝ) ^ 2 * T.leastEnergy)
          * (T.Z ((m : ℝ) ^ 2) - 1))
      atTop (𝓝 (T.leastEnergyMult : ℝ)) :=
  (T.tendsto_exp_mul_Z_sub_one hnt).comp
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)

end PartitionTower

end Theaetetus
