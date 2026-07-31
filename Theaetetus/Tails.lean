import Theaetetus.Certification

/-! # Certified Boltzmann tails

Lattice Boltzmann sums are computed numerically by truncating
`ℤ^r` to a finite box; certifying the numbers means bounding what
the truncation discards. The scalar tail beyond radius `N` is
geometrically dominated:
`∑_{|m|>N} e^{−αm²} ≤ 2·e^{−α(N+1)²}·(1 − e^{−2α(N+1)})⁻¹`
(`theta_tail_le`). For a quadratic action with a certified positive
eigenvalue lower bound `μ`, coercivity
(`QuadraticAction.mul_sum_sq_le_energy`) dominates every Boltzmann
weight by a product of scalar Gaussians, and a union bound over an
escaping coordinate reduces the lattice tail outside the sup-norm
box to `r` copies of the scalar tail, each padded by a full theta
factor for every remaining coordinate (`QuadraticAction.tail_le`).
The resulting split of the partition function into box plus
certified tail (`QuadraticAction.partFn_le_box_add_tail`) is the
shape a truncated numeric evaluation consumes. -/

namespace Theaetetus

open Matrix

/-! ## The scalar tail -/

/-- Summability of the shifted Gaussian tail. -/
private theorem summable_tail_shift {α : ℝ} (hα : 0 < α) (N : ℕ) :
    Summable (fun t : ℕ => Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2)) := by
  have hinj : Function.Injective (fun t : ℕ => (N : ℤ) + 1 + t) := by
    intro a b hab
    simpa using hab
  refine ((summable_theta α hα).comp_injective hinj).congr fun t => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-- Geometric domination of the shifted tail:
`e^{−α(N+1+t)²} ≤ e^{−α(N+1)²}·(e^{−2α(N+1)})ᵗ`. -/
private theorem tail_shift_le_geo {α : ℝ} (hα : 0 < α) (N : ℕ) (t : ℕ) :
    Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2)
      ≤ Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * Real.exp (-(2 * α * ((N : ℝ) + 1))) ^ t := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hα.le (sq_nonneg (t : ℝ)),
    (Nat.cast_nonneg t : (0 : ℝ) ≤ (t : ℝ)),
    (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]

/-- The geometric bound on the one-sided tail sum. -/
private theorem tsum_tail_shift_le {α : ℝ} (hα : 0 < α) (N : ℕ) :
    (∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2))
      ≤ Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * (1 - Real.exp (-(2 * α * ((N : ℝ) + 1))))⁻¹ := by
  have hq0 : (0 : ℝ) ≤ Real.exp (-(2 * α * ((N : ℝ) + 1))) :=
    (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * α * ((N : ℝ) + 1))) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have hgeo : Summable
      (fun t : ℕ => Real.exp (-(2 * α * ((N : ℝ) + 1))) ^ t) :=
    summable_geometric_of_lt_one hq0 hq1
  calc (∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2))
      ≤ ∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * Real.exp (-(2 * α * ((N : ℝ) + 1))) ^ t :=
        (summable_tail_shift hα N).tsum_le_tsum (tail_shift_le_geo hα N)
          (hgeo.mul_left _)
    _ = Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * ∑' t : ℕ, Real.exp (-(2 * α * ((N : ℝ) + 1))) ^ t :=
        hgeo.tsum_mul_left _
    _ = Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * (1 - Real.exp (-(2 * α * ((N : ℝ) + 1))))⁻¹ := by
        rw [tsum_geometric_of_lt_one hq0 hq1]

/-- **The scalar Boltzmann tail**: the two-sided integer tail beyond
radius `N` is dominated by twice the leading Boltzmann factor times
the geometric closing factor. -/
theorem theta_tail_le {α : ℝ} (hα : 0 < α) (N : ℕ) :
    (∑' m : ℤ, if (N : ℤ) < |m| then Real.exp (-α * (m : ℝ) ^ 2) else 0)
      ≤ 2 * (Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * (1 - Real.exp (-(2 * α * ((N : ℝ) + 1))))⁻¹) := by
  have hpos : HasSum
      (fun n : ℕ => if (N : ℤ) < |((n : ℤ) + 1)| then
          Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) else 0)
      (∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2)) := by
    have hinj : Function.Injective (fun t : ℕ => N + t) := fun a b h => by
      simpa using h
    have hvanish : ∀ n ∉ Set.range (fun t : ℕ => N + t),
        (if (N : ℤ) < |((n : ℤ) + 1)| then
            Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) else 0) = 0 := by
      intro n hn
      have hnN : n < N := by
        by_contra h
        exact hn ⟨n - N, by show N + (n - N) = n; omega⟩
      have hcond : ¬ (N : ℤ) < |((n : ℤ) + 1)| := by
        rw [abs_of_nonneg (by positivity)]
        omega
      rw [if_neg hcond]
    rw [← hinj.hasSum_iff hvanish]
    have hfeq : ((fun n : ℕ => if (N : ℤ) < |((n : ℤ) + 1)| then
        Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) else 0)
          ∘ (fun t : ℕ => N + t))
        = fun t : ℕ => Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2) := by
      funext t
      simp only [Function.comp_apply]
      have hcond : (N : ℤ) < |(((N + t : ℕ) : ℤ) + 1)| := by
        rw [abs_of_nonneg (by positivity)]
        push_cast
        omega
      rw [if_pos hcond]
      congr 1
      push_cast
      ring
    rw [hfeq]
    exact (summable_tail_shift hα N).hasSum
  have hneg : HasSum
      (fun n : ℕ => if (N : ℤ) < |(-((n : ℤ) + 1))| then
          Real.exp (-α * (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) else 0)
      (∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2)) := by
    have heq : (fun n : ℕ => if (N : ℤ) < |(-((n : ℤ) + 1))| then
        Real.exp (-α * (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) else 0)
        = fun n : ℕ => if (N : ℤ) < |((n : ℤ) + 1)| then
            Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) else 0 := by
      funext n
      rw [abs_neg]
      by_cases hc : (N : ℤ) < |((n : ℤ) + 1)|
      · rw [if_pos hc, if_pos hc]
        congr 1
        push_cast
        ring
      · rw [if_neg hc, if_neg hc]
    rw [heq]
    exact hpos
  have hZ : HasSum (fun m : ℤ =>
      if (N : ℤ) < |m| then Real.exp (-α * (m : ℝ) ^ 2) else 0)
      ((∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2))
        + (if (N : ℤ) < |(0 : ℤ)| then
            Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2) else 0)
        + ∑' t : ℕ, Real.exp (-α * ((N : ℝ) + 1 + t) ^ 2)) :=
    HasSum.of_add_one_of_neg_add_one hpos hneg
  have h0 : (if (N : ℤ) < |(0 : ℤ)| then
      Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2) else 0) = 0 := by
    have hcond : ¬ (N : ℤ) < |(0 : ℤ)| := by
      rw [abs_zero]
      omega
    rw [if_neg hcond]
  rw [hZ.tsum_eq, h0]
  linarith [tsum_tail_shift_le hα N]

/-! ## The lattice tail -/

/-- **The lattice Boltzmann tail**: outside the sup-norm box of
radius `N`, the Boltzmann sum of a quadratic action with a
certified positive eigenvalue lower bound `μ` is dominated by `r`
copies of the scalar tail, each padded by a full theta factor for
every remaining coordinate. -/
theorem QuadraticAction.tail_le {r : ℕ} (A : QuadraticAction r)
    {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-A.energy k.1))
      ≤ (r : ℝ) * theta μ ^ (r - 1)
          * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) := by
  set gauss : ℤ → ℝ := fun m => Real.exp (-μ * (m : ℝ) ^ 2) with hgauss
  set tailg : ℤ → ℝ := fun m =>
    if (N : ℤ) < |m| then Real.exp (-μ * (m : ℝ) ^ 2) else 0 with htailg
  have hgauss_nn : ∀ m, 0 ≤ gauss m := fun m => (Real.exp_pos _).le
  have htailg_nn : ∀ m, 0 ≤ tailg m := fun m => by
    simp only [htailg]
    split_ifs
    · positivity
    · exact le_rfl
  have htailg_le : ∀ m, tailg m ≤ gauss m := fun m => by
    simp only [htailg, hgauss]
    split_ifs
    · exact le_rfl
    · positivity
  have hgauss_sum : Summable gauss := by
    rw [hgauss]
    exact summable_theta μ hμ0
  have htailg_sum : Summable tailg :=
    Summable.of_nonneg_of_le htailg_nn htailg_le hgauss_sum
  have htheta : (∑' m : ℤ, gauss m) = theta μ := by
    rw [hgauss]
    rfl
  have hfam_nn : ∀ (i j : Fin r) (m : ℤ),
      0 ≤ (if j = i then tailg else gauss) m := fun i j m => by
    by_cases hj : j = i
    · rw [if_pos hj]
      exact htailg_nn m
    · rw [if_neg hj]
      exact hgauss_nn m
  have hfam_sum : ∀ i j : Fin r,
      Summable (if j = i then tailg else gauss) := fun i j => by
    by_cases hj : j = i
    · rw [if_pos hj]
      exact htailg_sum
    · rw [if_neg hj]
      exact hgauss_sum
  have hP_sum : ∀ i : Fin r, Summable (fun k : Fin r → ℤ =>
      ∏ j, (if j = i then tailg else gauss) (k j)) := fun i =>
    QuadraticAction.summable_finPi_prod r _
      (fun j m => hfam_nn i j m) (fun j => hfam_sum i j)
  have hpoint : ∀ k : Fin r → ℤ,
      Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-A.energy k)) k
        ≤ ∑ i, ∏ j, (if j = i then tailg else gauss) (k j) := by
    intro k
    by_cases hk : k ∈ {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
    · rw [Set.indicator_of_mem hk]
      obtain ⟨i₀, hi₀⟩ : ∃ i, (N : ℤ) < |k i| := by
        by_contra hno
        push Not at hno
        exact hk fun i => hno i
      have hdom : Real.exp (-A.energy k) ≤ ∏ j, gauss (k j) := by
        have hE := A.mul_sum_sq_le_energy hμ k
        calc Real.exp (-A.energy k)
            ≤ Real.exp (-(μ * ∑ j, (k j : ℝ) ^ 2)) := by
              apply Real.exp_le_exp.mpr
              linarith
          _ = ∏ j, gauss (k j) := by
              simp only [hgauss]
              rw [← Real.exp_sum]
              congr 1
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun j _ => by ring
      have hswitch : (∏ j, gauss (k j))
          = ∏ j, (if j = i₀ then tailg else gauss) (k j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = i₀
        · subst hj
          rw [if_pos rfl]
          simp only [hgauss, htailg]
          rw [if_pos hi₀]
        · rw [if_neg hj]
      calc Real.exp (-A.energy k)
          ≤ ∏ j, gauss (k j) := hdom
        _ = ∏ j, (if j = i₀ then tailg else gauss) (k j) := hswitch
        _ ≤ ∑ i, ∏ j, (if j = i then tailg else gauss) (k j) :=
            Finset.single_le_sum
              (fun i _ => Finset.prod_nonneg fun j _ => hfam_nn i j (k j))
              (Finset.mem_univ i₀)
    · rw [Set.indicator_of_notMem hk]
      exact Finset.sum_nonneg fun i _ =>
        Finset.prod_nonneg fun j _ => hfam_nn i j (k j)
  have hind_sum : Summable
      (Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
        (fun k => Real.exp (-A.energy k))) := by
    have hsum : Summable fun k : Fin r → ℤ => Real.exp (-A.energy k) :=
      A.summable.congr fun k => rfl
    refine Summable.of_nonneg_of_le
      (fun k => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) k)
      (fun k => ?_) hsum
    by_cases hk : k ∈ {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
    · exact le_of_eq (Set.indicator_of_mem hk _)
    · rw [Set.indicator_of_notMem hk]
      positivity
  have hswap : HasSum (fun k : Fin r → ℤ =>
      ∑ i, ∏ j, (if j = i then tailg else gauss) (k j))
      (∑ i, ∑' k : Fin r → ℤ,
        ∏ j, (if j = i then tailg else gauss) (k j)) :=
    hasSum_sum fun i _ => (hP_sum i).hasSum
  have hsub : (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
      Real.exp (-A.energy k.1))
      = ∑' k : Fin r → ℤ,
        Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-A.energy k)) k :=
    tsum_subtype {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
      (fun k => Real.exp (-A.energy k))
  rw [hsub]
  calc (∑' k : Fin r → ℤ,
        Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-A.energy k)) k)
      ≤ ∑' k : Fin r → ℤ,
          ∑ i, ∏ j, (if j = i then tailg else gauss) (k j) :=
        hind_sum.tsum_le_tsum hpoint hswap.summable
    _ = ∑ i, ∑' k : Fin r → ℤ,
          ∏ j, (if j = i then tailg else gauss) (k j) := hswap.tsum_eq
    _ = ∑ _i : Fin r, (∑' m : ℤ, tailg m) * theta μ ^ (r - 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [QuadraticAction.tsum_finPi_prod r _
          (fun j m => hfam_nn i j m) (fun j => hfam_sum i j)]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => ∑' m : ℤ, (if j = i then tailg else gauss) m)
          (Finset.mem_univ i)]
        congr 1
        · rw [if_pos rfl]
        · calc (∏ j ∈ Finset.univ.erase i,
                ∑' m : ℤ, (if j = i then tailg else gauss) m)
              = ∏ _j ∈ Finset.univ.erase i, theta μ :=
                Finset.prod_congr rfl fun j hj => by
                  rw [if_neg (Finset.ne_of_mem_erase hj), htheta]
            _ = theta μ ^ (r - 1) := by
                rw [Finset.prod_const,
                  Finset.card_erase_of_mem (Finset.mem_univ i),
                  Finset.card_univ, Fintype.card_fin]
    _ = (r : ℝ) * ((∑' m : ℤ, tailg m) * theta μ ^ (r - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ (r : ℝ) * ((2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
            * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹))
          * theta μ ^ (r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
        apply mul_le_mul_of_nonneg_right _
          (pow_nonneg (theta_pos μ hμ0).le _)
        simp only [htailg]
        exact theta_tail_le hμ0 N
    _ = (r : ℝ) * theta μ ^ (r - 1)
          * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) := by
        ring

/-- **The box approximation**: the partition function splits into
the sup-norm box of radius `N` plus a tail dominated by the
certified bound — the shape a truncated numeric evaluation
consumes. -/
theorem QuadraticAction.partFn_le_box_add_tail {r : ℕ}
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    A.toSectorAction.partFn
      ≤ (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
        + (r : ℝ) * theta μ ^ (r - 1)
            * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
                * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) := by
  have hsum : Summable fun k : Fin r → ℤ => Real.exp (-A.energy k) :=
    A.summable.congr fun k => rfl
  have hsplit : (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-A.energy k.1))
      + (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
      = A.toSectorAction.partFn :=
    hsum.tsum_subtype_add_tsum_subtype_compl
      {k : Fin r → ℤ | ∀ i, |k i| ≤ (N : ℤ)}
  rw [← hsplit]
  exact add_le_add le_rfl (A.tail_le hμ0 hμ N)

/-- **The certified enclosure**: the partition function lies in the
closed interval from the box sum to the box sum plus the certified
tail — the object an interval-arithmetic evaluation consumes. -/
theorem QuadraticAction.partFn_mem_box_Icc {r : ℕ}
    (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    A.toSectorAction.partFn ∈ Set.Icc
      (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-A.energy k.1))
      ((∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
        + (r : ℝ) * theta μ ^ (r - 1)
            * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
                * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹))) := by
  constructor
  · have hsum : Summable fun k : Fin r → ℤ => Real.exp (-A.energy k) :=
      A.summable.congr fun k => rfl
    have hsplit : (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
        + (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
            Real.exp (-A.energy k.1))
        = A.toSectorAction.partFn :=
      hsum.tsum_subtype_add_tsum_subtype_compl
        {k : Fin r → ℤ | ∀ i, |k i| ≤ (N : ℤ)}
    have htail_nn : (0 : ℝ)
        ≤ ∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
            Real.exp (-A.energy k.1) :=
      tsum_nonneg fun k => (Real.exp_pos _).le
    linarith [hsplit]
  · exact A.partFn_le_box_add_tail hμ0 hμ N

end Theaetetus
