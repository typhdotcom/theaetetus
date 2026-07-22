import Theaetetus.Defect

/-! # The reflection law: duality as a symmetry of the defect

**The defect is a weight-zero combination** (README: the symmetry).
Each factor `log θ(q²s)` carries modular weight — the Jacobi
duality multiplies `θ` by a prefactor — but the cross-ratio weighs
its four terms `½ + ½ − ½ − ½`, and the prefactors cancel exactly
because `gcd·lcm = q·q′`. What survives is an exact reflection law
(`defect_dual`):

    D_s(q, q′) = D_{π²/(s·lcm²)}(q/g, q′/g),    g := gcd(q, q′).

Every pair reflects onto its coprime reduction at a dual scale. On
a coprime pair the involution fixes the pair and moves only the
scale (`defect_scale_even`), so each coprime entry is an even
function of `log s` about its own center `s* = π/(qq′)`.

The engine is the real-variable rectangle reflection
(`theta_rect_dual`): the two Jacobi prefactor products of the
theta cross-ratio at couplings `{t, a²t, b²t, (ab)²t}` agree —
their quotient is one — because `(a²t)·(b²t) = t·((ab)²t)`. Both
all-scale sign proofs (`Sign`, branch two; `Submodular`,
reflection branch) re-derive this cancellation inline for their
own pair; this module states it once, and `theta_rect_lt_iff`
packages it as the inequality equivalence the reflection branches
actually consume. Ladder rungs 1–3. -/

namespace Theaetetus

/-- **The rectangle reflection** (rung 1): the theta cross-ratio at
couplings `{t, a²t, b²t, (ab)²t}` is invariant under the Jacobi
involution `t ↦ t′ = π²/((ab)²t)`, stated multiplicatively. The
four duality prefactors `(·/π)^(1/2)` cancel between the sides
because `(a²t)·(b²t) = t·((ab)²t)` — the `gcd·lcm = q·q′` identity
in real variables. -/
theorem theta_rect_dual {t t' a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (ht' : t' = Real.pi ^ 2 / ((a * b) ^ 2 * t)) :
    theta (a ^ 2 * t') * theta (b ^ 2 * t') * (theta t * theta ((a * b) ^ 2 * t))
      = theta (a ^ 2 * t) * theta (b ^ 2 * t)
        * (theta t' * theta ((a * b) ^ 2 * t')) := by
  subst ht'
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have ht0 : t ≠ 0 := ht.ne'
  -- the involution permutes the four couplings
  have h1 : a ^ 2 * (Real.pi ^ 2 / ((a * b) ^ 2 * t)) = Real.pi ^ 2 / (b ^ 2 * t) := by
    field_simp
  have h2 : b ^ 2 * (Real.pi ^ 2 / ((a * b) ^ 2 * t)) = Real.pi ^ 2 / (a ^ 2 * t) := by
    field_simp
  have h3 : (a * b) ^ 2 * (Real.pi ^ 2 / ((a * b) ^ 2 * t)) = Real.pi ^ 2 / t := by
    field_simp
  rw [h1, h2, h3, theta_duality_real (b ^ 2 * t) (by positivity),
      theta_duality_real (a ^ 2 * t) (by positivity),
      theta_duality_real ((a * b) ^ 2 * t) (by positivity),
      theta_duality_real t ht]
  -- the four prefactors cancel: (b²t/π)·(a²t/π) = ((ab)²t/π)·(t/π)
  have key : (b ^ 2 * t / Real.pi) ^ ((1 : ℝ) / 2)
        * (a ^ 2 * t / Real.pi) ^ ((1 : ℝ) / 2)
      = ((a * b) ^ 2 * t / Real.pi) ^ ((1 : ℝ) / 2)
        * (t / Real.pi) ^ ((1 : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
        ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  linear_combination
    (theta (a ^ 2 * t) * theta (b ^ 2 * t) * theta t * theta ((a * b) ^ 2 * t)) * key

/-- **The reflection as an inequality equivalence**: the
cross-ratio comparison at scale `t` and at the reflected scale
`t′` are the same strict inequality — the positivity and
cancellation bookkeeping of the reflection branches, centralized.
-/
theorem theta_rect_lt_iff {t t' a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (ht' : t' = Real.pi ^ 2 / ((a * b) ^ 2 * t)) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t) < theta t * theta ((a * b) ^ 2 * t)
      ↔ theta (a ^ 2 * t') * theta (b ^ 2 * t')
        < theta t' * theta ((a * b) ^ 2 * t') := by
  have key := theta_rect_dual ht ha hb ht'
  have ht'0 : 0 < t' := by rw [ht']; positivity
  have hR : 0 < theta t * theta ((a * b) ^ 2 * t) :=
    mul_pos (theta_pos _ ht) (theta_pos _ (by positivity))
  have hR' : 0 < theta t' * theta ((a * b) ^ 2 * t') :=
    mul_pos (theta_pos _ ht'0) (theta_pos _ (by positivity))
  constructor
  · intro h
    have h2 := mul_lt_mul_of_pos_right h hR'
    rw [← key] at h2
    rw [mul_comm (theta t * theta ((a * b) ^ 2 * t))
        (theta t' * theta ((a * b) ^ 2 * t'))] at h2
    exact lt_of_mul_lt_mul_right h2 hR.le
  · intro h
    have h2 := mul_lt_mul_of_pos_right h hR
    rw [key] at h2
    rw [mul_comm (theta t' * theta ((a * b) ^ 2 * t'))
        (theta t * theta ((a * b) ^ 2 * t))] at h2
    exact lt_of_mul_lt_mul_right h2 hR'.le

/-- **The reflection law** (rung 2): the defect of any pair equals
the defect of its coprime reduction at the reflected scale
`π²/(s·lcm²)`. The scaling prefactors cancel through
`gcd·lcm = q·q′` — the defect is weight-zero data. -/
theorem defect_dual {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    defect s q q' =
      defect (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
        (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  -- arithmetic of the reduction
  have hg : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hq
  have hgq : Nat.gcd q q' ∣ q := Nat.gcd_dvd_left q q'
  have hgq' : Nat.gcd q q' ∣ q' := Nat.gcd_dvd_right q q'
  have ha : 0 < q / Nat.gcd q q' := Nat.div_pos (Nat.le_of_dvd hq hgq) hg
  have hb : 0 < q' / Nat.gcd q q' := Nat.div_pos (Nat.le_of_dvd hq' hgq') hg
  have hqa : q / Nat.gcd q q' * Nat.gcd q q' = q := Nat.div_mul_cancel hgq
  have hq'b : q' / Nat.gcd q q' * Nat.gcd q q' = q' := Nat.div_mul_cancel hgq'
  have hco : Nat.Coprime (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
    Nat.coprime_div_gcd_div_gcd hg
  have hl : Nat.lcm q q'
      = q / Nat.gcd q q' * (q' / Nat.gcd q q') * Nat.gcd q q' := by
    refine Nat.eq_of_mul_eq_mul_left hg ?_
    calc Nat.gcd q q' * Nat.lcm q q' = q * q' := Nat.gcd_mul_lcm q q'
      _ = (q / Nat.gcd q q' * Nat.gcd q q')
          * (q' / Nat.gcd q q' * Nat.gcd q q') := by rw [hqa, hq'b]
      _ = Nat.gcd q q'
          * (q / Nat.gcd q q' * (q' / Nat.gcd q q') * Nat.gcd q q') := by ring
  have hlpos : 0 < Nat.lcm q q' := by
    rw [hl]; exact Nat.mul_pos (Nat.mul_pos ha hb) hg
  -- the same facts over ℝ
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hg
  have hlR0 : (0 : ℝ) < (Nat.lcm q q' : ℝ) := by exact_mod_cast hlpos
  have haR0 : (0 : ℝ) < ((q / Nat.gcd q q' : ℕ) : ℝ) := by exact_mod_cast ha
  have hbR0 : (0 : ℝ) < ((q' / Nat.gcd q q' : ℕ) : ℝ) := by exact_mod_cast hb
  have haR : ((q / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ) = (q : ℝ) := by
    exact_mod_cast hqa
  have hbR : ((q' / Nat.gcd q q' : ℕ) : ℝ) * (Nat.gcd q q' : ℝ) = (q' : ℝ) := by
    exact_mod_cast hq'b
  have hlR : (Nat.lcm q q' : ℝ)
      = ((q / Nat.gcd q q' : ℕ) : ℝ) * ((q' / Nat.gcd q q' : ℕ) : ℝ)
        * (Nat.gcd q q' : ℝ) := by exact_mod_cast hl
  -- instantiate the rectangle at the reduced pair over the gcd scale
  have hlink : Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s)
      = Real.pi ^ 2
        / ((((q / Nat.gcd q q' : ℕ) : ℝ) * ((q' / Nat.gcd q q' : ℕ) : ℝ)) ^ 2
          * ((Nat.gcd q q' : ℝ) ^ 2 * s)) := by
    rw [hlR]; ring_nf
  have key := theta_rect_dual (t := (Nat.gcd q q' : ℝ) ^ 2 * s)
    (t' := Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
    (a := ((q / Nat.gcd q q' : ℕ) : ℝ)) (b := ((q' / Nat.gcd q q' : ℕ) : ℝ))
    (by positivity) haR0 hbR0 hlink
  -- the unprimed couplings collapse to the original pair
  have A1 : ((q / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * ((Nat.gcd q q' : ℝ) ^ 2 * s)
      = (q : ℝ) ^ 2 * s := by rw [← haR]; ring
  have A2 : ((q' / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * ((Nat.gcd q q' : ℝ) ^ 2 * s)
      = (q' : ℝ) ^ 2 * s := by rw [← hbR]; ring
  have A3 : (((q / Nat.gcd q q' : ℕ) : ℝ) * ((q' / Nat.gcd q q' : ℕ) : ℝ)) ^ 2
        * ((Nat.gcd q q' : ℝ) ^ 2 * s)
      = (Nat.lcm q q' : ℝ) ^ 2 * s := by rw [hlR]; ring
  rw [A1, A2, A3] at key
  -- positivity of the eight theta values
  have hT1 : theta ((q : ℝ) ^ 2 * s) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have hT2 : theta ((q' : ℝ) ^ 2 * s) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have hT3 : theta ((Nat.gcd q q' : ℝ) ^ 2 * s) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have hT4 : theta ((Nat.lcm q q' : ℝ) ^ 2 * s) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have ht' : (0 : ℝ) < Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s) := by positivity
  have hT5 : theta (((q / Nat.gcd q q' : ℕ) : ℝ) ^ 2
      * (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have hT6 : theta (((q' / Nat.gcd q q' : ℕ) : ℝ) ^ 2
      * (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  have hT7 : theta (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s)) ≠ 0 :=
    (theta_pos _ ht').ne'
  have hT8 : theta ((((q / Nat.gcd q q' : ℕ) : ℝ)
        * ((q' / Nat.gcd q q' : ℕ) : ℝ)) ^ 2
      * (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))) ≠ 0 :=
    (theta_pos _ (by positivity)).ne'
  -- take logs of the rectangle identity
  have klog := congrArg Real.log key
  rw [Real.log_mul (mul_ne_zero hT5 hT6) (mul_ne_zero hT3 hT4),
      Real.log_mul hT5 hT6, Real.log_mul hT3 hT4,
      Real.log_mul (mul_ne_zero hT1 hT2) (mul_ne_zero hT7 hT8),
      Real.log_mul hT1 hT2, Real.log_mul hT7 hT8] at klog
  -- assemble the two defects
  unfold defect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco]
  push_cast
  simp only [one_pow, one_mul]
  linarith [klog]

/-- **Coprime evenness** (rung 3): on a coprime pair the reflection
fixes the pair and moves only the scale, `s ↦ π²/(s·(pq)²)` — each
coprime defect entry is an even function of `log s` about its own
center `s* = π/(pq)`. -/
theorem defect_scale_even {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hco : Nat.Coprime p q) :
    defect s p q = defect (Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s)) p q := by
  have h := defect_dual hs hp hq
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco] at h
  simpa [Nat.div_one, Nat.cast_mul] using h

end Theaetetus
