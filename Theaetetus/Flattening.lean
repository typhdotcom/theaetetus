import Theaetetus.Kernel

/-! # The large-scale chamber: saturation flattens the kernel

**Rung 5** (README: Q4 and the ladder). Beyond the absolute
threshold `s ≥ 1` the prime pairing is conditionally negative
definite on **every** finite prime set at once
(`pairing_cnd_large`) — the uniform, dimension-free half of Q4's
chamber structure.

The proof starts from the exact zero-sum identity
(`quadFormOn_pairing_eq`): the quadratic form is the
product-kernel form minus the diagonal of Q5 curvatures. Writing
`z = e^{−s} ≤ 1/2`:

* every product-kernel entry is submultiplicative —
  `log θ((pq)²s) ≤ (32/15)·e^{−sp²}e^{−sq²}` via
  `(pq)² ≥ p² + q²` (`log_theta_sq_prod_le`);
* Cauchy–Schwarz and the geometric tail
  `∑_P e^{−2sp²} ≤ (4/3)z⁴` (`tail_sq_le`) bound the
  product-kernel form by `(128/45)·z⁴·‖c‖²`, dimension-free;
* each diagonal curvature is at least `z − (64/15)z⁴`
  (`q5_diag_lower`), the base mode beating the resolved ones.

The closure is `64z³ ≤ 9`, comfortable at `z ≤ 1/2`. Everything
is per-`‖c‖²`: no entrywise perturbation, no dependence on the
size of the prime set. -/

namespace Theaetetus

/-- At scales `s ≥ 1` the modulus is at most `1/2` — the single
numeric input, through `e > 2`. -/
private theorem exp_neg_le_half {s : ℝ} (hs : 1 ≤ s) :
    Real.exp (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  calc Real.exp (-s) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
    _ = 1 / Real.exp 1 := inv_eq_one_div _
    _ ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2.le

/-- **Submultiplicative entry bound**: every product-kernel entry
is dominated by the product of the per-prime modes,
`log θ((pq)²s) ≤ (32/15)·e^{−sp²}·e^{−sq²}` — from
`(pq)² ≥ p² + q²` and the geometric tail at coupling `≥ 16s`. -/
theorem log_theta_sq_prod_le {s : ℝ} (hs : 1 ≤ s) {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) :
    Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ 32 / 15 * (Real.exp (-(s * (p : ℝ) ^ 2))
        * Real.exp (-(s * (q : ℝ) ^ 2))) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hX0 : (0 : ℝ) < ((p : ℝ) * (q : ℝ)) ^ 2 * s := by positivity
  have hpq4 : (4 : ℝ) ≤ (p : ℝ) * (q : ℝ) := by nlinarith
  have hsq16 : (16 : ℝ) ≤ ((p : ℝ) * (q : ℝ)) ^ 2 := by nlinarith [hpq4]
  have h16 : 16 * s ≤ ((p : ℝ) * (q : ℝ)) ^ 2 * s := by
    nlinarith [hsq16, hs0]
  have h1 : Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ theta (((p : ℝ) * (q : ℝ)) ^ 2 * s) - 1 :=
    Real.log_le_sub_one_of_pos (theta_pos _ hX0)
  have h2 := theta_le _ hX0
  have hhalf : Real.exp (-s) ≤ 1 / 2 := exp_neg_le_half hs
  have hXexp : Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ Real.exp (-s) ^ 16 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hz16 : Real.exp (-s) ^ 16 ≤ 1 / 16 := by
    calc Real.exp (-s) ^ 16 ≤ Real.exp (-s) ^ 4 :=
          pow_le_pow_of_le_one (Real.exp_pos _).le (by linarith)
            (by norm_num)
      _ ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le hhalf 4
      _ ≤ 1 / 16 := by norm_num
  have hden : (15 : ℝ) / 16
      ≤ 1 - Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)) := by
    linarith [hXexp.trans hz16]
  have hE := (Real.exp_pos (-(((p : ℝ) * (q : ℝ)) ^ 2 * s))).le
  have hfrac : Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s))
        / (1 - Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)))
      ≤ Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)) * (16 / 15) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hden, hE]
  have hsub : Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ Real.exp (-(s * (p : ℝ) ^ 2)) * Real.exp (-(s * (q : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hq4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hple : (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≤ ((p : ℝ) * (q : ℝ)) ^ 2 := by
      nlinarith [hp4, hq4]
    nlinarith [hple, hs0]
  calc Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
      ≤ theta (((p : ℝ) * (q : ℝ)) ^ 2 * s) - 1 := h1
    _ ≤ 2 * (Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s))
        / (1 - Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)))) := by linarith
    _ ≤ 2 * (Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)) * (16 / 15)) := by
        linarith
    _ = 32 / 15 * Real.exp (-(((p : ℝ) * (q : ℝ)) ^ 2 * s)) := by ring
    _ ≤ 32 / 15 * (Real.exp (-(s * (p : ℝ) ^ 2))
        * Real.exp (-(s * (q : ℝ) ^ 2))) := by nlinarith [hsub]

/-- **The diagonal lower bound**: every Q5 curvature on the
diagonal is at least `e^{−s} − (64/15)e^{−4s}` — the base mode
beats the resolved corrections. -/
theorem q5_diag_lower {s : ℝ} (hs : 1 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    Real.exp (-s) - 64 / 15 * Real.exp (-s) ^ 4
      ≤ Real.log (theta s)
        + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
        - 2 * Real.log (theta ((p : ℝ) ^ 2 * s)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hz0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hhalf : Real.exp (-s) ≤ 1 / 2 := exp_neg_le_half hs
  -- base: log θ(s) ≥ e^{−s}
  have hθ0 : (0 : ℝ) < theta s := theta_pos s hs0
  have hbase : Real.exp (-s) ≤ Real.log (theta s) := by
    have hθ := theta_ge s hs0
    have hlog := Real.one_sub_inv_le_log_of_pos hθ0
    have key : Real.exp (-s) * theta s ≤ theta s - 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ)
        (by linarith : (0 : ℝ) ≤ 1 - Real.exp (-s)),
        mul_nonneg hz0.le
          (by linarith : (0 : ℝ) ≤ 1 - 2 * Real.exp (-s))]
    have h5 : Real.exp (-s) ≤ (theta s - 1) / theta s :=
      (le_div_iff₀ hθ0).mpr key
    have h6 : (theta s - 1) / theta s = 1 - (theta s)⁻¹ := by
      rw [sub_div, div_self hθ0.ne', one_div]
    linarith [h6 ▸ h5]
  -- middle: log θ((p·p)²s) ≥ 0
  have hmid : (0 : ℝ) ≤ Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s)) :=
    Real.log_nonneg (theta_gt_one _ (by positivity)).le
  -- right: log θ(p²s) ≤ (32/15)·e^{−4s}
  have hright : Real.log (theta ((p : ℝ) ^ 2 * s))
      ≤ 32 / 15 * Real.exp (-s) ^ 4 := by
    have h4s : (0 : ℝ) < 4 * s := by linarith
    have hanti : theta ((p : ℝ) ^ 2 * s) ≤ theta (4 * s) := by
      apply theta_anti h4s
      have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      nlinarith [hp4, hs0]
    have hlog : Real.log (theta ((p : ℝ) ^ 2 * s))
        ≤ Real.log (theta (4 * s)) :=
      Real.log_le_log (theta_pos _ (by positivity)) hanti
    have h1 := Real.log_le_sub_one_of_pos (theta_pos _ h4s)
    have h2 := theta_le _ h4s
    have hexp4 : Real.exp (-(4 * s)) = Real.exp (-s) ^ 4 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hz4 : Real.exp (-s) ^ 4 ≤ 1 / 16 := by
      calc Real.exp (-s) ^ 4 ≤ (1 / 2) ^ 4 :=
            pow_le_pow_left₀ hz0.le hhalf 4
        _ ≤ 1 / 16 := by norm_num
    have hden : (15 : ℝ) / 16 ≤ 1 - Real.exp (-(4 * s)) := by
      rw [hexp4]; linarith
    have hfrac : Real.exp (-(4 * s)) / (1 - Real.exp (-(4 * s)))
        ≤ Real.exp (-(4 * s)) * (16 / 15) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [(Real.exp_pos (-(4 * s))).le, hden]
    calc Real.log (theta ((p : ℝ) ^ 2 * s))
        ≤ Real.log (theta (4 * s)) := hlog
      _ ≤ theta (4 * s) - 1 := h1
      _ ≤ 2 * (Real.exp (-(4 * s)) / (1 - Real.exp (-(4 * s)))) := by
          linarith
      _ ≤ 2 * (Real.exp (-(4 * s)) * (16 / 15)) := by linarith
      _ = 32 / 15 * Real.exp (-(4 * s)) := by ring
      _ = 32 / 15 * Real.exp (-s) ^ 4 := by rw [hexp4]
  linarith

/-- **The dimension-free tail**: over any finite set of naturals
`≥ 2`, the squared modes sum to at most `(4/3)e^{−4s}` — via
`2p² ≥ 4 + 2p` and the geometric series, uniformly in the set. -/
theorem tail_sq_le {s : ℝ} (hs : 1 ≤ s) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2)
      ≤ 4 / 3 * Real.exp (-s) ^ 4 := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hz0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hhalf : Real.exp (-s) ≤ 1 / 2 := exp_neg_le_half hs
  have hterm : ∀ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2
      ≤ Real.exp (-s) ^ 4 * (Real.exp (-s) ^ 2) ^ p := by
    intro p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hp
    have hL : Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2
        = Real.exp (2 * -(s * (p : ℝ) ^ 2)) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hR : Real.exp (-s) ^ 4 * (Real.exp (-s) ^ 2) ^ p
        = Real.exp ((4 + 2 * (p : ℝ)) * -s) := by
      rw [← pow_mul, ← pow_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hL, hR]
    apply Real.exp_le_exp.mpr
    have h2p : 4 + 2 * (p : ℝ) ≤ 2 * (p : ℝ) ^ 2 := by nlinarith
    nlinarith [h2p, hs0]
  have hr0 : (0 : ℝ) ≤ Real.exp (-s) ^ 2 := by positivity
  have hr1 : Real.exp (-s) ^ 2 ≤ 1 / 4 := by
    calc Real.exp (-s) ^ 2 ≤ (1 / 2) ^ 2 :=
          pow_le_pow_left₀ hz0.le hhalf 2
      _ = 1 / 4 := by norm_num
  have hgeo : (∑ p ∈ P, (Real.exp (-s) ^ 2) ^ p) ≤ 4 / 3 := by
    have hsubset : P ⊆ Finset.range (P.sup id + 1) := by
      intro p hp
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.le_sup (f := id) hp))
    have h1 : (∑ p ∈ P, (Real.exp (-s) ^ 2) ^ p)
        ≤ ∑ p ∈ Finset.range (P.sup id + 1), (Real.exp (-s) ^ 2) ^ p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        fun i _ _ => pow_nonneg hr0 i
    have hG0 : (0 : ℝ)
        ≤ ∑ p ∈ Finset.range (P.sup id + 1), (Real.exp (-s) ^ 2) ^ p :=
      Finset.sum_nonneg fun i _ => pow_nonneg hr0 i
    have hmul := geom_sum_mul (Real.exp (-s) ^ 2) (P.sup id + 1)
    have hpow : (0 : ℝ) ≤ (Real.exp (-s) ^ 2) ^ (P.sup id + 1) :=
      pow_nonneg hr0 _
    nlinarith [hmul, hpow, hG0, h1, hr0, hr1]
  calc (∑ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2)
      ≤ ∑ p ∈ P, Real.exp (-s) ^ 4 * (Real.exp (-s) ^ 2) ^ p :=
        Finset.sum_le_sum hterm
    _ = Real.exp (-s) ^ 4 * ∑ p ∈ P, (Real.exp (-s) ^ 2) ^ p := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-s) ^ 4 * (4 / 3) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 4 / 3 * Real.exp (-s) ^ 4 := by ring

/-- **THE LARGE-SCALE CHAMBER** (rung 5): beyond the absolute
threshold `s ≥ 1` the prime pairing is conditionally negative
definite on every finite prime set — saturation flattens the
kernel, uniformly and dimension-free. The closure is `64z³ ≤ 9`
at `z = e^{−s} ≤ 1/2`. -/
theorem pairing_cnd_large {s : ℝ} (hs : 1 ≤ s) {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    IsCNDOn (pairing s) P := by
  intro c hc
  have hs0 : (0 : ℝ) < s := by linarith
  have hz0 : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hhalf : Real.exp (-s) ≤ 1 / 2 := exp_neg_le_half hs
  rw [quadFormOn_pairing_eq hprime hc]
  have hc2 : (0 : ℝ) ≤ ∑ p ∈ P, c p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  -- the product-kernel form against the weighted modes
  have hstep : (∑ p ∈ P, ∑ q ∈ P, c p * c q
        * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)))
      ≤ ∑ p ∈ P, ∑ q ∈ P, 32 / 15
        * ((|c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
          * (|c q| * Real.exp (-(s * (q : ℝ) ^ 2)))) := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    have hL0 : (0 : ℝ)
        ≤ Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) := by
      have hp0 : 0 < p := (hprime p hp).pos
      have hq0 : 0 < q := (hprime q hq).pos
      have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
      have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
      exact Real.log_nonneg (theta_gt_one _ (by positivity)).le
    have hentry := log_theta_sq_prod_le hs (hprime p hp).two_le
      (hprime q hq).two_le
    calc c p * c q * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s))
        ≤ |c p * c q| * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hL0
      _ = |c p| * |c q| * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) := by
          rw [abs_mul]
      _ ≤ |c p| * |c q| * (32 / 15 * (Real.exp (-(s * (p : ℝ) ^ 2))
          * Real.exp (-(s * (q : ℝ) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hentry (by positivity)
      _ = 32 / 15 * ((|c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
          * (|c q| * Real.exp (-(s * (q : ℝ) ^ 2)))) := by ring
  have hcollapse : (∑ p ∈ P, ∑ q ∈ P, 32 / 15
        * ((|c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
          * (|c q| * Real.exp (-(s * (q : ℝ) ^ 2)))))
      = 32 / 15 * ((∑ p ∈ P, |c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
        * (∑ q ∈ P, |c q| * Real.exp (-(s * (q : ℝ) ^ 2)))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
  -- Cauchy–Schwarz
  have hCS : (∑ p ∈ P, |c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
        * (∑ q ∈ P, |c q| * Real.exp (-(s * (q : ℝ) ^ 2)))
      ≤ (∑ p ∈ P, c p ^ 2)
        * (∑ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq P (fun p => |c p|)
      (fun p => Real.exp (-(s * (p : ℝ) ^ 2)))
    have hsq : (∑ p ∈ P, |c p| ^ 2) = ∑ p ∈ P, c p ^ 2 :=
      Finset.sum_congr rfl fun p _ => sq_abs _
    calc (∑ p ∈ P, |c p| * Real.exp (-(s * (p : ℝ) ^ 2)))
          * (∑ q ∈ P, |c q| * Real.exp (-(s * (q : ℝ) ^ 2)))
        = (∑ p ∈ P, |c p| * Real.exp (-(s * (p : ℝ) ^ 2))) ^ 2 :=
          (pow_two _).symm
      _ ≤ (∑ p ∈ P, |c p| ^ 2)
          * (∑ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2) := h
      _ = (∑ p ∈ P, c p ^ 2)
          * (∑ p ∈ P, Real.exp (-(s * (p : ℝ) ^ 2)) ^ 2) := by rw [hsq]
  have htail := tail_sq_le hs fun p hp => (hprime p hp).two_le
  -- the diagonal from below
  have hDsum : (Real.exp (-s) - 64 / 15 * Real.exp (-s) ^ 4)
        * (∑ p ∈ P, c p ^ 2)
      ≤ ∑ p ∈ P, c p ^ 2
        * (Real.log (theta s)
          + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
          - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) := by
    rw [mul_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_left
      (q5_diag_lower hs (hprime p hp).two_le) (sq_nonneg _)
  -- assemble
  have hHfinal : (∑ p ∈ P, ∑ q ∈ P, c p * c q
        * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)))
      ≤ 32 / 15 * ((∑ p ∈ P, c p ^ 2) * (4 / 3 * Real.exp (-s) ^ 4)) := by
    refine (hstep.trans (le_of_eq hcollapse)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (hCS.trans (mul_le_mul_of_nonneg_left htail hc2)) (by norm_num)
  have hz3 : Real.exp (-s) ^ 3 ≤ 1 / 8 := by
    calc Real.exp (-s) ^ 3 ≤ (1 / 2) ^ 3 :=
          pow_le_pow_left₀ hz0.le hhalf 3
      _ = 1 / 8 := by norm_num
  have hz4c : Real.exp (-s) ^ 4 * (∑ p ∈ P, c p ^ 2)
      ≤ 1 / 8 * (Real.exp (-s) * (∑ p ∈ P, c p ^ 2)) := by
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hz3 hz0.le) hc2]
  nlinarith [hHfinal, hDsum, hz4c, mul_nonneg hz0.le hc2]

end Theaetetus
