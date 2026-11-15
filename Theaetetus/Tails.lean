import Theaetetus.Certification

/-! # Certified Boltzmann tails

Lattice Boltzmann sums are computed numerically by truncating
`ℤ^r` to a finite box; certifying the numbers means bounding what
the truncation discards. The scalar tail beyond radius `N` is
geometrically dominated:
`∑_{|m|>N} e^{−αm²} ≤ 2·e^{−α(N+1)²}·(1 − e^{−2α(N+1)})⁻¹`
(`theta_tail_le`). The lattice tail is a union bound over an
escaping coordinate: any energy dominating `ν·∑kᵢ²` has its
Boltzmann sum outside the sup-norm box bounded by `r` copies of
the scalar tail, each padded by a full theta factor for every
remaining coordinate (`tail_exp_le`). A quadratic action with a
certified positive eigenvalue lower bound `μ` instantiates this
through coercivity (`QuadraticAction.tail_le`), the partition
function splits into box plus certified truncation error
(`QuadraticAction.partFn_le_box_add_tail`,
`QuadraticAction.partFn_mem_box_Icc`), and polynomial energy
weights are absorbed at half the coupling —
`xᵐ·e^{−x} ≤ 2ᵐ·m!·e^{−x/2}` — so every energy-moment tail is an
instance of the plain tail at `μ/2`
(`QuadraticAction.moment_tail_le`). -/

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
      rw [ite_eq_right hcond]
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
      rw [ite_eq_left hcond]
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
      · rw [ite_eq_left hc, ite_eq_left hc]
        congr 1
        push_cast
        ring
      · rw [ite_eq_right hc, ite_eq_right hc]
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
    rw [ite_eq_right hcond]
  rw [hZ.tsum_eq, h0]
  linarith [tsum_tail_shift_le hα N]

/-! ## The lattice tail -/

/-- **The lattice Boltzmann tail, coercive form**: any energy
dominating `ν·∑kᵢ²` has its Boltzmann sum outside the sup-norm box
of radius `N` bounded by `r` copies of the scalar tail, each padded
by a full theta factor for every remaining coordinate. The escape
is a union bound over the escaping coordinate, and each escaping
term is itself a product weight, evaluated exactly by
`QuadraticAction.tsum_finPi_prod`. -/
theorem tail_exp_le {r : ℕ} {E : (Fin r → ℤ) → ℝ} {ν : ℝ}
    (hν : 0 < ν)
    (hcoer : ∀ k : Fin r → ℤ, ν * ∑ i, (k i : ℝ) ^ 2 ≤ E k)
    (N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-E k.1))
      ≤ (r : ℝ) * theta ν ^ (r - 1)
          * (2 * (Real.exp (-ν * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * ν * ((N : ℝ) + 1))))⁻¹)) := by
  set gauss : ℤ → ℝ := fun m => Real.exp (-ν * (m : ℝ) ^ 2) with hgauss
  set tailg : ℤ → ℝ := fun m =>
    if (N : ℤ) < |m| then Real.exp (-ν * (m : ℝ) ^ 2) else 0 with htailg
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
    exact summable_theta ν hν
  have htailg_sum : Summable tailg :=
    Summable.of_nonneg_of_le htailg_nn htailg_le hgauss_sum
  have htheta : (∑' m : ℤ, gauss m) = theta ν := by
    rw [hgauss]
    rfl
  have hgdom : ∀ k : Fin r → ℤ,
      Real.exp (-E k) ≤ ∏ j, gauss (k j) := by
    intro k
    calc Real.exp (-E k)
        ≤ Real.exp (-(ν * ∑ j, (k j : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have := hcoer k
          linarith
      _ = ∏ j, gauss (k j) := by
          simp only [hgauss]
          rw [← Real.exp_sum]
          congr 1
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hEsum : Summable fun k : Fin r → ℤ => Real.exp (-E k) :=
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hgdom
      (QuadraticAction.summable_finPi_prod r (fun _ => gauss)
        (fun _ m => hgauss_nn m) (fun _ => hgauss_sum))
  have hfam_nn : ∀ (i j : Fin r) (m : ℤ),
      0 ≤ (if j = i then tailg else gauss) m := fun i j m => by
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      exact htailg_nn m
    · rw [ite_eq_right hj]
      exact hgauss_nn m
  have hfam_sum : ∀ i j : Fin r,
      Summable (if j = i then tailg else gauss) := fun i j => by
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      exact htailg_sum
    · rw [ite_eq_right hj]
      exact hgauss_sum
  have hP_sum : ∀ i : Fin r, Summable (fun k : Fin r → ℤ =>
      ∏ j, (if j = i then tailg else gauss) (k j)) := fun i =>
    QuadraticAction.summable_finPi_prod r _
      (fun j m => hfam_nn i j m) (fun j => hfam_sum i j)
  have hpoint : ∀ k : Fin r → ℤ,
      Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-E k)) k
        ≤ ∑ i, ∏ j, (if j = i then tailg else gauss) (k j) := by
    intro k
    by_cases hk : k ∈ {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
    · rw [Set.indicator_of_mem hk]
      obtain ⟨i₀, hi₀⟩ : ∃ i, (N : ℤ) < |k i| := by
        by_contra hno
        push Not at hno
        exact hk fun i => hno i
      have hswitch : (∏ j, gauss (k j))
          = ∏ j, (if j = i₀ then tailg else gauss) (k j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = i₀
        · subst hj
          rw [ite_eq_left rfl]
          simp only [hgauss, htailg]
          rw [ite_eq_left hi₀]
        · rw [ite_eq_right hj]
      calc Real.exp (-E k)
          ≤ ∏ j, gauss (k j) := hgdom k
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
        (fun k => Real.exp (-E k))) := by
    refine Summable.of_nonneg_of_le
      (fun k => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) k)
      (fun k => ?_) hEsum
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
      Real.exp (-E k.1))
      = ∑' k : Fin r → ℤ,
        Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-E k)) k :=
    tsum_subtype {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
      (fun k => Real.exp (-E k))
  rw [hsub]
  calc (∑' k : Fin r → ℤ,
        Set.indicator {k : Fin r → ℤ | ¬ ∀ i, |k i| ≤ (N : ℤ)}
          (fun k => Real.exp (-E k)) k)
      ≤ ∑' k : Fin r → ℤ,
          ∑ i, ∏ j, (if j = i then tailg else gauss) (k j) :=
        hind_sum.tsum_le_tsum hpoint hswap.summable
    _ = ∑ i, ∑' k : Fin r → ℤ,
          ∏ j, (if j = i then tailg else gauss) (k j) := hswap.tsum_eq
    _ = ∑ _i : Fin r, (∑' m : ℤ, tailg m) * theta ν ^ (r - 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [QuadraticAction.tsum_finPi_prod r _
          (fun j m => hfam_nn i j m) (fun j => hfam_sum i j)]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => ∑' m : ℤ, (if j = i then tailg else gauss) m)
          (Finset.mem_univ i)]
        congr 1
        · rw [ite_eq_left rfl]
        · calc (∏ j ∈ Finset.univ.erase i,
                ∑' m : ℤ, (if j = i then tailg else gauss) m)
              = ∏ _j ∈ Finset.univ.erase i, theta ν :=
                Finset.prod_congr rfl fun j hj => by
                  rw [ite_eq_right (Finset.ne_of_mem_erase hj), htheta]
            _ = theta ν ^ (r - 1) := by
                rw [Finset.prod_const,
                  Finset.card_erase_of_mem (Finset.mem_univ i),
                  Finset.card_univ, Fintype.card_fin]
    _ = (r : ℝ) * ((∑' m : ℤ, tailg m) * theta ν ^ (r - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ (r : ℝ) * ((2 * (Real.exp (-ν * ((N : ℝ) + 1) ^ 2)
            * (1 - Real.exp (-(2 * ν * ((N : ℝ) + 1))))⁻¹))
          * theta ν ^ (r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
        apply mul_le_mul_of_nonneg_right _
          (pow_nonneg (theta_pos ν hν).le _)
        simp only [htailg]
        exact theta_tail_le hν N
    _ = (r : ℝ) * theta ν ^ (r - 1)
          * (2 * (Real.exp (-ν * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * ν * ((N : ℝ) + 1))))⁻¹)) := by
        ring

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
              * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) :=
  tail_exp_le (E := A.energy) hμ0
    (fun k => A.mul_sum_sq_le_energy hμ k) N

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

/-! ## Moment tails -/

/-- Factorial absorption of a polynomial weight into half the
exponent: `xᵐ·e^{−x} ≤ 2ᵐ·m!·e^{−x/2}` for `x ≥ 0`. -/
private theorem pow_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ m * Real.exp (-x)
      ≤ 2 ^ m * (m.factorial : ℝ) * Real.exp (-(x / 2)) := by
  have hhalf : (0 : ℝ) ≤ x / 2 := by linarith
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast m.factorial_pos
  have hser : (x / 2) ^ m / (m.factorial : ℝ) ≤ Real.exp (x / 2) := by
    calc (x / 2) ^ m / (m.factorial : ℝ)
        ≤ ∑ i ∈ Finset.range (m + 1), (x / 2) ^ i / (i.factorial : ℝ) :=
          Finset.single_le_sum
            (f := fun i => (x / 2) ^ i / (i.factorial : ℝ))
            (fun i _ => div_nonneg (pow_nonneg hhalf i)
              (Nat.cast_nonneg _))
            (Finset.mem_range.mpr (Nat.lt_succ_self m))
      _ ≤ Real.exp (x / 2) := Real.sum_le_exp_of_nonneg hhalf (m + 1)
  have hpow : x ^ m ≤ 2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2) := by
    have h1 : (x / 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (x / 2) := by
      rw [div_le_iff₀ hfac] at hser
      linarith
    have h2 : x ^ m = 2 ^ m * (x / 2) ^ m := by
      rw [← mul_pow]
      congr 1
      ring
    rw [h2]
    calc 2 ^ m * (x / 2) ^ m
        ≤ 2 ^ m * ((m.factorial : ℝ) * Real.exp (x / 2)) := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2) := by ring
  calc x ^ m * Real.exp (-x)
      ≤ (2 ^ m * (m.factorial : ℝ) * Real.exp (x / 2)) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 2 ^ m * (m.factorial : ℝ) * Real.exp (-(x / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The lattice moment tail**: outside the sup-norm box, the
`m`-th energy-moment Boltzmann sum of a certified action is
dominated by the factorial constant times the plain tail at half
the certified coupling. -/
theorem QuadraticAction.moment_tail_le {r : ℕ} (A : QuadraticAction r)
    {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (m N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        A.energy k.1 ^ m * Real.exp (-A.energy k.1))
      ≤ 2 ^ m * (m.factorial : ℝ)
          * ((r : ℝ) * theta (μ / 2) ^ (r - 1)
              * (2 * (Real.exp (-(μ / 2) * ((N : ℝ) + 1) ^ 2)
                  * (1 - Real.exp (-(2 * (μ / 2) * ((N : ℝ) + 1))))⁻¹))) := by
  have hμ2 : (0 : ℝ) < μ / 2 := by linarith
  have hcoer : ∀ k : Fin r → ℤ,
      (μ / 2) * ∑ i, (k i : ℝ) ^ 2 ≤ A.energy k / 2 := by
    intro k
    have := A.mul_sum_sq_le_energy hμ k
    linarith
  have htail := tail_exp_le (E := fun k => A.energy k / 2) hμ2 hcoer N
  have habs : ∀ k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
      A.energy k.1 ^ m * Real.exp (-A.energy k.1)
        ≤ 2 ^ m * (m.factorial : ℝ) * Real.exp (-(A.energy k.1 / 2)) :=
    fun k => pow_mul_exp_neg_le (A.energy_nonneg k.1) m
  have hhalf_sum : Summable fun k : Fin r → ℤ =>
      Real.exp (-(A.energy k / 2)) := by
    refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
      (fun k => ?_)
      (QuadraticAction.summable_finPi_prod r
        (fun _ => fun z : ℤ => Real.exp (-(μ / 2) * (z : ℝ) ^ 2))
        (fun _ z => (Real.exp_pos _).le)
        (fun _ => summable_theta _ hμ2))
    calc Real.exp (-(A.energy k / 2))
        ≤ Real.exp (-((μ / 2) * ∑ j, (k j : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have := hcoer k
          linarith
      _ = ∏ j, Real.exp (-(μ / 2) * (k j : ℝ) ^ 2) := by
          rw [← Real.exp_sum]
          congr 1
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hmom_sum : Summable
      fun k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)} =>
        A.energy k.1 ^ m * Real.exp (-A.energy k.1) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (A.energy_nonneg k.1) m)
        (Real.exp_pos _).le)
      habs ((hhalf_sum.subtype _).mul_left _)
  calc (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        A.energy k.1 ^ m * Real.exp (-A.energy k.1))
      ≤ ∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
          2 ^ m * (m.factorial : ℝ) * Real.exp (-(A.energy k.1 / 2)) :=
        hmom_sum.tsum_le_tsum habs ((hhalf_sum.subtype _).mul_left _)
    _ = 2 ^ m * (m.factorial : ℝ)
          * ∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
              Real.exp (-(A.energy k.1 / 2)) :=
        (hhalf_sum.subtype _).tsum_mul_left _
    _ ≤ 2 ^ m * (m.factorial : ℝ)
          * ((r : ℝ) * theta (μ / 2) ^ (r - 1)
              * (2 * (Real.exp (-(μ / 2) * ((N : ℝ) + 1) ^ 2)
                  * (1 - Real.exp (-(2 * (μ / 2) * ((N : ℝ) + 1))))⁻¹))) := by
        apply mul_le_mul_of_nonneg_left htail (by positivity)

end Theaetetus
