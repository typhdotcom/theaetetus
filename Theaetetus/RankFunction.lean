import Theaetetus.Submodular

/-! # Residue complexity as a rank function

**Q5(a), first formal content.** The rank-one residue complexity

    K_s(q) := log θ(s) − log θ(q²s)

(the description cost of the mod-`q` reduction: harmonic complexity
minus the log modal weight, per `residueAction_complexity_eq` in the
carrier layer, evaluated on the rank-one carrier) satisfies the
polymatroid rank axioms on the divisibility lattice:

* **normalized** — `K(1) = 0` (`resComplexity_one`);
* **monotone along divisibility** — `q ∣ q′ ⇒ K(q) ≤ K(q′)`
  (`resComplexity_mono`);
* **submodular** — `K(gcd) + K(lcm) ≤ K(q) + K(q′)`
  (`resComplexity_submodular`), **strictly** off chains
  (`resComplexity_strictSubmodular`, = Q1).

So `q ↦ K_s(q)` is a polymatroid-like rank function whose
independence defect is exactly the defect matrix. Q5's remaining
question — non-Shannon inequalities among higher defects — starts
from this object. -/

namespace Theaetetus

/-- **The residue complexity** `K_s(q) = log θ(s) − log θ(q²s)`:
the description cost of resolving the rank-one carrier mod `q`. -/
noncomputable def resComplexity (s : ℝ) (q : ℕ) : ℝ :=
  Real.log (theta s) - Real.log (theta ((q : ℝ) ^ 2 * s))

/-- Normalization: the trivial resolution costs nothing. -/
theorem resComplexity_one (s : ℝ) : resComplexity s 1 = 0 := by
  unfold resComplexity
  norm_num

/-- Nonnegativity: every resolution costs. -/
theorem resComplexity_nonneg {s : ℝ} (hs : 0 < s) {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ resComplexity s q := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hanti : theta ((q : ℝ) ^ 2 * s) ≤ theta s := by
    apply theta_anti hs
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (q : ℝ) + 1)) hs.le]
  have := Real.log_le_log (theta_pos _ (by positivity)) hanti
  unfold resComplexity
  linarith

/-- **Monotonicity along divisibility**: refining a resolution can
only cost more — `q ∣ q′` implies `K(q) ≤ K(q′)`. -/
theorem resComplexity_mono {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hdvd : q ∣ q')
    (hq' : q' ≠ 0) : resComplexity s q ≤ resComplexity s q' := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq' (zero_dvd_iff.mp hdvd)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq0
  have hq0R : (0 : ℝ) < (q : ℝ) := by linarith
  have hqle : (q : ℝ) ≤ (q' : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq') hdvd
  have hanti : theta ((q' : ℝ) ^ 2 * s) ≤ theta ((q : ℝ) ^ 2 * s) := by
    apply theta_anti (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (q' : ℝ) - (q : ℝ))
      (by linarith : (0 : ℝ) ≤ (q' : ℝ) + (q : ℝ))) hs.le]
  have := Real.log_le_log (theta_pos _ (by positivity)) hanti
  unfold resComplexity
  linarith

/-- **Submodularity** (Q1 rearranged): residue complexity is a
submodular function on the divisibility lattice —
`K(gcd) + K(lcm) ≤ K(q) + K(q′)` for every pair. -/
theorem resComplexity_submodular {s : ℝ} (hs : 0 < s) (q q' : ℕ) :
    resComplexity s (Nat.gcd q q') + resComplexity s (Nat.lcm q q')
      ≤ resComplexity s q + resComplexity s q' := by
  have h := defect_nonpos hs q q'
  unfold defect at h
  unfold resComplexity
  linarith

/-- **Strict submodularity off chains** — the rank function's
independence defect is strict at every incomparable pair. -/
theorem resComplexity_strictSubmodular {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    resComplexity s (Nat.gcd q q') + resComplexity s (Nat.lcm q q')
      < resComplexity s q + resComplexity s q' := by
  have h := defect_neg_of_incomparable hs hqq' hq'q
  unfold defect at h
  unfold resComplexity
  linarith

end Theaetetus
