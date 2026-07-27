import Theaetetus.Defect
import Theaetetus.Duality
import Theaetetus.ThetaBounds
import Theaetetus.Witness
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Strict submodularity: the sign at every incomparable pair

**Q1 at rank one, closed** (`defect_neg_of_incomparable`): for every
scale `s > 0` and every incomparable pair `q, q′` of resolutions,

    D_s(q, q′) < 0.

Together with chain-vanishing (`defect_eq_zero_of_dvd`) this gives
the complete characterization (`defect_eq_zero_iff`): **the defect
detects divisibility** — `D_s(q,q′) = 0` iff `q ∣ q′` or `q′ ∣ q`.
Writing `h(q) = log θ(q²s)`, the function `h` is strictly
supermodular off chains, equivalently residue complexity is a
strictly submodular function on the divisibility lattice. M3 proved
the pair `(2,3)`; this file proves the lattice.

Reduction: dividing out the gcd (`t := gcd²·s`, `a := q/gcd`,
`b := q′/gcd`) the claim is the theta-value inequality

    θ(a²t)·θ(b²t) < θ(t)·θ((ab)²t)     (`theta_prod_lt_general`)

for real `2 ≤ a < b`, `t > 0` — incomparability enters only as
`a, b ≥ 2`. Three regimes:

* **Geometric branch** (`π ≤ a²t`): both left couplings exceed `π`,
  so `θ ≤ 1 + (21/10)e^{−α}` (`theta_le_of_three_le`) applies; the
  excess of the left side decays like `e^{−t}·e^{−2}` per factor and
  the single first mode `2e^{−t}` of `θ(t)` beats it.
* **Duality-comparison branch** (`a²t ≤ π ≤ abt`): a one-sided
  Jacobi flip. The inverse duality `θ(α) = (π/α)^½·θ(π²/α)`
  (`theta_dual_form`) gives `θ(t) ≥ a·θ(a²t)/θ(3)` — the scaling
  regime concentrates mass in the coarse factor at exact rate `a` —
  while `θ(b²t), θ(π²/(a²t)) ≤ θ(3)`. The branch closes on the
  single numeric fact `θ(3)² < 2 ≤ a` (`theta_three_sq_lt_two`).
* **Reflection** (`abt < π`): the involution `t ↦ π²/((ab)²t)` maps
  the configuration to one with `abt′ > π` and swaps the roles of
  the two sides; the four Jacobi prefactors cancel between the sides
  because `1·(ab)² = a²·b²` — the `gcd·lcm = q·q′` identity again,
  consumed as `theta_rect_lt_iff`.

The pair `(2,3)` never had a duality-comparison regime — its two
branches met at `π > 3`. The general pair needs the third regime
because for `ab` large the involution's fixed point `t* = π/(ab)`
sits far below the geometric branch's threshold: between them the
aspect ratio `b/a` is arbitrary, and only the exact rate `a` from
the one-sided flip survives it. -/

namespace Theaetetus

/-! ## The inverse duality and two theta estimates -/

/-- The duality read from the large-coupling side:
`θ(α) = (π/α)^½ · θ(π²/α)`. For `α ≤ π` the dual coupling `π²/α`
exceeds `π`, so this expresses a small-coupling theta value by a
tame one times an exact scaling prefactor. -/
theorem theta_dual_form {α : ℝ} (hα : 0 < α) :
    theta α = (Real.pi / α) ^ ((1 : ℝ) / 2) * theta (Real.pi ^ 2 / α) := by
  have h := theta_duality_real (Real.pi ^ 2 / α) (by positivity)
  rw [show Real.pi ^ 2 / (Real.pi ^ 2 / α) = α from by
        rw [div_div_eq_mul_div,
          mul_div_cancel_left₀ _ (by positivity : (Real.pi ^ 2 : ℝ) ≠ 0)],
      show Real.pi ^ 2 / α / Real.pi = Real.pi / α from by
        rw [div_div, div_eq_div_iff (by positivity) (by positivity)]; ring] at h
  exact h

/-- Linear-coefficient tail bound past coupling `3`:
`θ(α) ≤ 1 + (21/10)·e^{−α}` for `α ≥ 3`. From the two-mode bound:
the tail `2e^{−4α}/(1−e^{−2α})` is at most `(1/10)e^{−α}` once
`e^{−3α} ≤ e^{−9} < 1/8000`. -/
theorem theta_le_of_three_le {α : ℝ} (hα : 3 ≤ α) :
    theta α ≤ 1 + 21 / 10 * Real.exp (-α) := by
  have h0 : (0 : ℝ) < α := by linarith
  have h := theta_le_two_mode h0
  have hx : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have h3 : Real.exp (-3) < 1 / 20 := exp_numeric_bounds.2.2
  have h3pos : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
  have hxx : Real.exp (-3) * Real.exp (-3) < 1 / 400 := by nlinarith
  have h6 : Real.exp (-(2 * α)) ≤ Real.exp (-3) * Real.exp (-3) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hden : (0 : ℝ) < 1 - Real.exp (-(2 * α)) := by linarith
  have h9 : Real.exp (-(3 * α)) ≤ Real.exp (-3) * Real.exp (-3) * Real.exp (-3) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have he9 : Real.exp (-3) * Real.exp (-3) * Real.exp (-3) < 1 / 8000 := by
    nlinarith
  have h4α : Real.exp (-(4 * α)) = Real.exp (-α) * Real.exp (-(3 * α)) := by
    rw [← Real.exp_add]; congr 1; ring
  have htail : Real.exp (-(4 * α)) / (1 - Real.exp (-(2 * α)))
      ≤ 1 / 20 * Real.exp (-α) := by
    rw [div_le_iff₀ hden, h4α]
    have hb1 : Real.exp (-(3 * α)) ≤ 1 / 8000 := le_of_lt (lt_of_le_of_lt h9 he9)
    nlinarith [mul_le_mul_of_nonneg_left hb1 hx.le,
      mul_le_mul_of_nonneg_left
        (show (399 : ℝ) / 400 ≤ 1 - Real.exp (-(2 * α)) from by linarith) hx.le]
  linarith

/-- The numeric pivot of the duality-comparison branch:
`θ(3)² < 2`. Numerically `θ(3)² ≈ 1.21`; the branch needs it below
the smallest admissible scaling rate `a = 2`. -/
theorem theta_three_sq_lt_two : theta 3 * theta 3 < 2 := by
  have h3 : Real.exp (-3) < 1 / 20 := exp_numeric_bounds.2.2
  have h3pos : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
  have hK := theta_le_of_three_le (le_refl (3 : ℝ))
  have hθpos : (0 : ℝ) < theta 3 := theta_pos 3 (by norm_num)
  have hθ : theta 3 < 1105 / 1000 := by nlinarith
  nlinarith

/-! ## The three regimes -/

/-- **Geometric branch**: if `π ≤ a²t` all four couplings on the
left exceed `π > 3`, each factor is `1 + O(e^{−α})`, and the first
mode `2e^{−t}` of `θ(t)` dominates the entire left excess: the
separations `a²t − t ≥ (3/4)π > 2` price every left mode below
`e^{−t}·e^{−2}`. -/
private theorem theta_prod_lt_of_geo {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a)
    (hab : a < b) (hhigh : Real.pi ≤ a ^ 2 * t) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t) < theta t * theta ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h3a : (3 : ℝ) ≤ a ^ 2 * t := by linarith
  have hab2 : a ^ 2 * t < b ^ 2 * t := by
    nlinarith [mul_pos (mul_pos (sub_pos.mpr hab)
      (show (0 : ℝ) < b + a by linarith)) ht]
  have h3b : (3 : ℝ) ≤ b ^ 2 * t := by linarith
  have h4a : 4 * t ≤ a ^ 2 * t := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr ha)
      (show (0 : ℝ) ≤ a + 2 by linarith)) ht.le]
  have h4b : 4 * t < b ^ 2 * t := by
    nlinarith [mul_pos (mul_pos (show (0 : ℝ) < b - 2 by linarith)
      (show (0 : ℝ) < b + 2 by linarith)) ht]
  have hsep_a : 2 < a ^ 2 * t - t := by linarith
  have hsep_b : 2 < b ^ 2 * t - t := by linarith
  have hu0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hu1 : Real.exp (-t) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hx : Real.exp (-(a ^ 2 * t)) < Real.exp (-t) * (1369 / 10000) := by
    have hsplit : Real.exp (-(a ^ 2 * t))
        = Real.exp (-t) * Real.exp (-(a ^ 2 * t - t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    exact mul_lt_mul_of_pos_left
      (lt_trans (Real.exp_lt_exp.mpr (by linarith)) exp_neg_two_lt) hu0
  have hy : Real.exp (-(b ^ 2 * t)) < Real.exp (-t) * (1369 / 10000) := by
    have hsplit : Real.exp (-(b ^ 2 * t))
        = Real.exp (-t) * Real.exp (-(b ^ 2 * t - t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    exact mul_lt_mul_of_pos_left
      (lt_trans (Real.exp_lt_exp.mpr (by linarith)) exp_neg_two_lt) hu0
  have hxpos : (0 : ℝ) < Real.exp (-(a ^ 2 * t)) := Real.exp_pos _
  have hypos : (0 : ℝ) < Real.exp (-(b ^ 2 * t)) := Real.exp_pos _
  have hKa := theta_le_of_three_le h3a
  have hKb := theta_le_of_three_le h3b
  have hbt0 : (0 : ℝ) < b ^ 2 * t := by positivity
  have habt0 : (0 : ℝ) < (a * b) ^ 2 * t := by positivity
  have hprod : theta (a ^ 2 * t) * theta (b ^ 2 * t)
      ≤ (1 + 21 / 10 * Real.exp (-(a ^ 2 * t)))
        * (1 + 21 / 10 * Real.exp (-(b ^ 2 * t))) :=
    mul_le_mul hKa hKb (theta_pos _ hbt0).le (by positivity)
  have huu : Real.exp (-t) * Real.exp (-t) < Real.exp (-t) :=
    mul_lt_of_lt_one_right hu0 hu1
  have hmid : (1 + 21 / 10 * Real.exp (-(a ^ 2 * t)))
      * (1 + 21 / 10 * Real.exp (-(b ^ 2 * t))) < 1 + 2 * Real.exp (-t) := by
    nlinarith [hx, hy, mul_lt_mul'' hx hy hxpos.le hypos.le, huu, hu0, hxpos, hypos]
  calc theta (a ^ 2 * t) * theta (b ^ 2 * t)
      ≤ (1 + 21 / 10 * Real.exp (-(a ^ 2 * t)))
        * (1 + 21 / 10 * Real.exp (-(b ^ 2 * t))) := hprod
    _ < 1 + 2 * Real.exp (-t) := hmid
    _ ≤ theta t := theta_ge t ht
    _ ≤ theta t * theta ((a * b) ^ 2 * t) :=
        le_mul_of_one_le_right (theta_pos t ht).le (theta_gt_one _ habt0).le

/-- **Duality-comparison branch**: if `a²t ≤ π ≤ abt` the coarse
pair `t, a²t` sits in the scaling regime, where the one-sided flip
`θ(t) = (π/t)^½·θ(π²/t) ≥ a·θ(a²t)/θ(3)` extracts the exact rate
`a ≥ 2`, while `θ(b²t) ≤ θ(3)` because `b²t ≥ abt ≥ π`. The branch
closes on `θ(3)² < 2`. -/
private theorem theta_prod_lt_of_dual {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a)
    (hab : a < b) (hmid : Real.pi ≤ a * b * t) (hlow : a ^ 2 * t ≤ Real.pi) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t) < theta t * theta ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hat0 : (0 : ℝ) < a ^ 2 * t := by positivity
  have hbt0 : (0 : ℝ) < b ^ 2 * t := by positivity
  have hb2t : Real.pi ≤ b ^ 2 * t := by
    have h1 : a * (b ^ 2 * t) = b * (a * b * t) := by ring
    have h2 : b * Real.pi ≤ b * (a * b * t) := mul_le_mul_of_nonneg_left hmid hb0.le
    have h3 : a * Real.pi ≤ b * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hπ0.le
    have h4 : a * Real.pi ≤ a * (b ^ 2 * t) := by linarith
    exact le_of_mul_le_mul_left h4 ha0
  have hθb3 : theta (b ^ 2 * t) ≤ theta 3 := theta_anti (by norm_num) (by linarith)
  have hdA := theta_dual_form hat0
  have hdT := theta_dual_form ht
  have hgeπ : Real.pi ≤ Real.pi ^ 2 / (a ^ 2 * t) := by
    rw [le_div_iff₀ hat0]
    nlinarith [mul_le_mul_of_nonneg_left hlow hπ0.le]
  have hθdA : theta (Real.pi ^ 2 / (a ^ 2 * t)) ≤ theta 3 :=
    theta_anti (by norm_num) (by linarith)
  have hθdT : (1 : ℝ) ≤ theta (Real.pi ^ 2 / t) := (theta_gt_one _ (by positivity)).le
  have hP0 : (0 : ℝ) < (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hQ0 : (0 : ℝ) < (Real.pi / t) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have haext : ((a ^ 2 : ℝ)) ^ ((1 : ℝ) / 2) = a := by
    rw [pow_two, Real.mul_rpow ha0.le ha0.le, ← Real.rpow_add ha0,
      show (1 : ℝ) / 2 + 1 / 2 = 1 from by norm_num, Real.rpow_one]
  have hfac : a * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2)
      = (Real.pi / t) ^ ((1 : ℝ) / 2) := by
    calc a * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2)
        = (a ^ 2) ^ ((1 : ℝ) / 2) * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) := by
          rw [haext]
      _ = (a ^ 2 * (Real.pi / (a ^ 2 * t))) ^ ((1 : ℝ) / 2) :=
          (Real.mul_rpow (by positivity) (by positivity)).symm
      _ = (Real.pi / t) ^ ((1 : ℝ) / 2) := by
          rw [show a ^ 2 * (Real.pi / (a ^ 2 * t)) = Real.pi / t from by
            rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
            ring]
  have hθa_le : theta (a ^ 2 * t)
      ≤ (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) * theta 3 := by
    rw [hdA]
    exact mul_le_mul_of_nonneg_left hθdA hP0.le
  have hθt_ge : (Real.pi / t) ^ ((1 : ℝ) / 2) ≤ theta t := by
    rw [hdT]
    exact le_mul_of_one_le_right hQ0.le hθdT
  have h2P : 2 * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) ≤ theta t := by
    have h5 : 2 * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2)
        ≤ a * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right ha hP0.le
    rw [hfac] at h5
    exact h5.trans hθt_ge
  have hθ30 : (0 : ℝ) < theta 3 := theta_pos 3 (by norm_num)
  calc theta (a ^ 2 * t) * theta (b ^ 2 * t)
      ≤ ((Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) * theta 3) * theta 3 :=
        mul_le_mul hθa_le hθb3 (theta_pos _ hbt0).le (mul_nonneg hP0.le hθ30.le)
    _ = (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) * (theta 3 * theta 3) := by ring
    _ < (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) * 2 :=
        mul_lt_mul_of_pos_left theta_three_sq_lt_two hP0
    _ = 2 * (Real.pi / (a ^ 2 * t)) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ theta t := h2P
    _ ≤ theta t * theta ((a * b) ^ 2 * t) :=
        le_mul_of_one_le_right (theta_pos t ht).le
          (theta_gt_one _ (by positivity)).le

/-- **The theta inequality at every pair** (Q1, rank one, ordered
form): for real `2 ≤ a < b` and every `t > 0`,
`θ(a²t)·θ(b²t) < θ(t)·θ((ab)²t)`. If `abt < π` the involution
`t ↦ π²/((ab)²t)` reflects the configuration into `abt′ > π` —
the four Jacobi prefactors cancel because `1·(ab)² = a²·b²` — and
there the two direct branches cover everything. -/
theorem theta_prod_lt_general {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a) (hab : a < b) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t) < theta t * theta ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  rcases le_or_gt Real.pi (a * b * t) with hmid | hmid
  · rcases le_or_gt (a ^ 2 * t) Real.pi with hlow | hhigh
    · exact theta_prod_lt_of_dual ht ha hab hmid hlow
    · exact theta_prod_lt_of_geo ht ha hab hhigh.le
  · -- reflect through `theta_rect_lt_iff`: `t′ = π²/((ab)²t)` has
    -- `abt′ ≥ π`, where the two direct branches cover everything
    have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
    have ht'0 : (0 : ℝ) < Real.pi ^ 2 / ((a * b) ^ 2 * t) := by positivity
    have habt' : Real.pi ≤ a * b * (Real.pi ^ 2 / ((a * b) ^ 2 * t)) := by
      rw [show a * b * (Real.pi ^ 2 / ((a * b) ^ 2 * t))
            = Real.pi ^ 2 / (a * b * t) from by
          rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
          ring,
        le_div_iff₀ (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hmid hπ0]
    rw [theta_rect_lt_iff ht ha0 hb0 rfl]
    rcases le_or_gt (a ^ 2 * (Real.pi ^ 2 / ((a * b) ^ 2 * t))) Real.pi
      with hlow' | hhigh'
    · exact theta_prod_lt_of_dual ht'0 ha hab habt' hlow'
    · exact theta_prod_lt_of_geo ht'0 ha hab hhigh'.le

/-- The theta inequality, symmetric form: `a, b ≥ 2` and `a ≠ b`. -/
theorem theta_prod_lt_general' {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hne : a ≠ b) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t) < theta t * theta ((a * b) ^ 2 * t) := by
  rcases hne.lt_or_gt with h | h
  · exact theta_prod_lt_general ht ha h
  · have hkey := theta_prod_lt_general ht hb h
    rw [show (b * a) ^ 2 * t = (a * b) ^ 2 * t from by ring] at hkey
    calc theta (a ^ 2 * t) * theta (b ^ 2 * t)
        = theta (b ^ 2 * t) * theta (a ^ 2 * t) := mul_comm _ _
      _ < theta t * theta ((a * b) ^ 2 * t) := hkey

/-! ## The sign on the divisibility lattice -/

/-- The defect at a gcd-normalized pair: `D_s(ga, gb) < 0` for
coprime `a, b ≥ 2`. -/
private theorem defect_neg_aux {s : ℝ} (hs : 0 < s) {g a b : ℕ} (hg : 0 < g)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hne : a ≠ b) (hco : Nat.Coprime a b) :
    defect s (g * a) (g * b) < 0 := by
  have hgcd : Nat.gcd (g * a) (g * b) = g := by
    rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hco, mul_one]
  have hlcm : Nat.lcm (g * a) (g * b) = g * (a * b) := by
    rw [Nat.lcm_mul_left, Nat.Coprime.lcm_eq_mul hco]
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have haR0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hbR0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hneR : (a : ℝ) ≠ (b : ℝ) := by exact_mod_cast hne
  have ht : (0 : ℝ) < (g : ℝ) ^ 2 * s := by positivity
  have hkey := theta_prod_lt_general' ht haR hbR hneR
  unfold defect
  rw [hgcd, hlcm,
    show ((g * a : ℕ) : ℝ) ^ 2 * s = (a : ℝ) ^ 2 * ((g : ℝ) ^ 2 * s) from by
      push_cast; ring,
    show ((g * b : ℕ) : ℝ) ^ 2 * s = (b : ℝ) ^ 2 * ((g : ℝ) ^ 2 * s) from by
      push_cast; ring,
    show ((g * (a * b) : ℕ) : ℝ) ^ 2 * s
        = ((a : ℝ) * (b : ℝ)) ^ 2 * ((g : ℝ) ^ 2 * s) from by
      push_cast; ring]
  have hp1 : (0 : ℝ) < theta ((a : ℝ) ^ 2 * ((g : ℝ) ^ 2 * s)) :=
    theta_pos _ (by positivity)
  have hp2 : (0 : ℝ) < theta ((b : ℝ) ^ 2 * ((g : ℝ) ^ 2 * s)) :=
    theta_pos _ (by positivity)
  have hp3 : (0 : ℝ) < theta ((g : ℝ) ^ 2 * s) := theta_pos _ ht
  have hp4 : (0 : ℝ) < theta (((a : ℝ) * (b : ℝ)) ^ 2 * ((g : ℝ) ^ 2 * s)) :=
    theta_pos _ (by positivity)
  have hlog := Real.log_lt_log (mul_pos hp1 hp2) hkey
  rw [Real.log_mul hp1.ne' hp2.ne', Real.log_mul hp3.ne' hp4.ne'] at hlog
  linarith

/-- **STRICT SUBMODULARITY** (Q1, rank one, closed): the defect is
strictly negative at **every** incomparable pair and **every** scale
— `D_s(q, q′) < 0` whenever neither of `q, q′` divides the other.
Residue complexity is a strictly submodular function on the
divisibility lattice: coupling two incomparable resolutions always
saves strictly more than their shared base. M3 proved one pair; this
is the lattice. -/
theorem defect_neg_of_incomparable {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) : defect s q q' < 0 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact hq'q (dvd_zero q')
  have hq'0 : q' ≠ 0 := by rintro rfl; exact hqq' (dvd_zero q)
  have hgpos : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left q' (Nat.pos_of_ne_zero hq0)
  have hco := Nat.coprime_div_gcd_div_gcd hgpos
  have haq : Nat.gcd q q' * (q / Nat.gcd q q') = q :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left q q')
  have hbq : Nat.gcd q q' * (q' / Nat.gcd q q') = q' :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right q q')
  have ha0 : q / Nat.gcd q q' ≠ 0 := by
    intro h; rw [h, mul_zero] at haq; exact hq0 haq.symm
  have ha1 : q / Nat.gcd q q' ≠ 1 := by
    intro h; rw [h, mul_one] at haq
    exact hqq' (haq ▸ Nat.gcd_dvd_right q q')
  have hb0 : q' / Nat.gcd q q' ≠ 0 := by
    intro h; rw [h, mul_zero] at hbq; exact hq'0 hbq.symm
  have hb1 : q' / Nat.gcd q q' ≠ 1 := by
    intro h; rw [h, mul_one] at hbq
    exact hq'q (hbq ▸ Nat.gcd_dvd_left q q')
  have ha2 : 2 ≤ q / Nat.gcd q q' := (Nat.two_le_iff _).mpr ⟨ha0, ha1⟩
  have hb2 : 2 ≤ q' / Nat.gcd q q' := (Nat.two_le_iff _).mpr ⟨hb0, hb1⟩
  have hne : q / Nat.gcd q q' ≠ q' / Nat.gcd q q' := by
    intro h
    have h2 : Nat.gcd q q' * (q / Nat.gcd q q')
        = Nat.gcd q q' * (q' / Nat.gcd q q') := by rw [h]
    rw [haq, hbq] at h2
    exact hqq' (dvd_of_eq h2)
  have hmain := defect_neg_aux hs hgpos ha2 hb2 hne hco
  rw [haq, hbq] at hmain
  exact hmain

/-- The defect is globally nonpositive: on chains it vanishes, off
them it is strictly negative. Residue complexity is submodular,
with no hypotheses on the pair. -/
theorem defect_nonpos {s : ℝ} (hs : 0 < s) (q q' : ℕ) : defect s q q' ≤ 0 := by
  by_cases h1 : q ∣ q'
  · exact (defect_eq_zero_of_dvd s h1).le
  by_cases h2 : q' ∣ q
  · rw [defect_comm]
    exact (defect_eq_zero_of_dvd s h2).le
  exact (defect_neg_of_incomparable hs h1 h2).le

/-- **THE DEFECT DETECTS DIVISIBILITY**: the kernel of the defect
matrix is exactly the chain relation — `D_s(q,q′) = 0` iff `q ∣ q′`
or `q′ ∣ q`. The complete characterization at rank one. -/
theorem defect_eq_zero_iff {s : ℝ} (hs : 0 < s) {q q' : ℕ} :
    defect s q q' = 0 ↔ q ∣ q' ∨ q' ∣ q := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd h (defect_neg_of_incomparable hs hcon.1 hcon.2).ne
  · rintro (h | h)
    · exact defect_eq_zero_of_dvd s h
    · rw [defect_comm]; exact defect_eq_zero_of_dvd s h

/-- Strictness characterized: `D_s(q,q′) < 0` iff the pair is
incomparable. -/
theorem defect_neg_iff {s : ℝ} (hs : 0 < s) {q q' : ℕ} :
    defect s q q' < 0 ↔ ¬q ∣ q' ∧ ¬q' ∣ q := by
  constructor
  · intro h
    by_contra hcon
    rw [not_and_or, not_not, not_not] at hcon
    rw [(defect_eq_zero_iff hs).mpr hcon] at h
    exact lt_irrefl 0 h
  · rintro ⟨h1, h2⟩
    exact defect_neg_of_incomparable hs h1 h2

end Theaetetus
