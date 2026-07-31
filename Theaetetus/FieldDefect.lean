import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Cast.Field

/-! # The field defect and the annihilation of affine log weights

The defect construction — the alternating sum of logarithms over
the resolution rectangle `{q, q′, gcd, lcm}` — applies to any
partition field `Z : ℝ → ℝ` (`fieldDefect`), before any analysis:
this module depends on nothing but logarithms and `gcd`/`lcm`
arithmetic. The scalar, tower, and Gram defects are instances
(`defect_eq_fieldDefect`, `PartitionTower.defect_eq_fieldDefect`,
`gramDefect_eq_fieldDefect`, recorded where those objects live),
and the structural laws are proved once here and inherited by
every instance: symmetry (`fieldDefect_comm`), vanishing on chains
(`fieldDefect_eq_zero_of_dvd`), and vanishing on the diagonal
(`fieldDefect_self`).

The law that carries the duality: **the defect annihilates affine
log weights** (`fieldDefect_dual_of_log_reflect`). If a reflection
sends `log Z′(π²/α)` to `log Z(α)` plus an affine weight
`a·log α + b`, the weight cancels in the four-term alternating
sum — the constant by sign count zero, the log-linear part by
`gcd·lcm = q·q′` — and the defect reflects with no weight at all.
Whatever normalization or modular weight a duality carries, the
defect does not see it; what survives reflection is
shape-sensitive information only. -/

namespace Theaetetus

/-- The defect of a partition field: the alternating sum of its
logarithms over the resolution rectangle `{q, q′, gcd, lcm}` at
scale `s`. -/
noncomputable def fieldDefect (Z : ℝ → ℝ) (s : ℝ) (q q' : ℕ) : ℝ :=
  (Real.log (Z ((q : ℝ) ^ 2 * s)) + Real.log (Z ((q' : ℝ) ^ 2 * s)))
    - (Real.log (Z ((Nat.gcd q q' : ℝ) ^ 2 * s))
      + Real.log (Z ((Nat.lcm q q' : ℝ) ^ 2 * s)))

/-- The field defect is symmetric in its resolutions. -/
theorem fieldDefect_comm (Z : ℝ → ℝ) (s : ℝ) (q q' : ℕ) :
    fieldDefect Z s q q' = fieldDefect Z s q' q := by
  unfold fieldDefect
  rw [Nat.gcd_comm, Nat.lcm_comm]
  ring

/-- **The field defect vanishes on chains**: along a divisibility
relation the pair `{gcd, lcm}` collapses to `{q, q′}` — pure
`gcd`/`lcm` algebra, before any analysis. -/
theorem fieldDefect_eq_zero_of_dvd (Z : ℝ → ℝ) (s : ℝ) {q q' : ℕ}
    (hdvd : q ∣ q') :
    fieldDefect Z s q q' = 0 := by
  unfold fieldDefect
  rw [Nat.gcd_eq_left hdvd,
    Nat.dvd_antisymm (Nat.lcm_dvd hdvd dvd_rfl) (Nat.dvd_lcm_right q q')]
  ring

/-- The field defect vanishes on the diagonal. -/
theorem fieldDefect_self (Z : ℝ → ℝ) (s : ℝ) (q : ℕ) :
    fieldDefect Z s q q = 0 :=
  fieldDefect_eq_zero_of_dvd Z s dvd_rfl

/-- **Reduction to the coprime base**: the field defect at any pair
of resolutions is the field defect at the reduced pair and the
`gcd²`-rescaled coupling — the four arguments coincide. -/
theorem fieldDefect_div_gcd (Z : ℝ → ℝ) (s : ℝ) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect Z s q q'
      = fieldDefect Z ((Nat.gcd q q' : ℝ) ^ 2 * s)
          (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  have hg : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hq
  have hgq : Nat.gcd q q' ∣ q := Nat.gcd_dvd_left q q'
  have hgq' : Nat.gcd q q' ∣ q' := Nat.gcd_dvd_right q q'
  have hco : Nat.Coprime (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
    Nat.coprime_div_gcd_div_gcd hg
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hg
  have hglqq : (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)
      = (q : ℝ) * (q' : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm q q'
  have haR : ((q / Nat.gcd q q' : ℕ) : ℝ)
      = (q : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq hgR.ne'
  have hbR : ((q' / Nat.gcd q q' : ℕ) : ℝ)
      = (q' : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq' hgR.ne'
  have e1 : ((q / Nat.gcd q q' : ℕ) : ℝ) ^ 2
      * ((Nat.gcd q q' : ℝ) ^ 2 * s) = (q : ℝ) ^ 2 * s := by
    rw [haR, div_pow]
    field_simp
  have e2 : ((q' / Nat.gcd q q' : ℕ) : ℝ) ^ 2
      * ((Nat.gcd q q' : ℝ) ^ 2 * s) = (q' : ℝ) ^ 2 * s := by
    rw [hbR, div_pow]
    field_simp
  have e3 : ((1 : ℕ) : ℝ) ^ 2 * ((Nat.gcd q q' : ℝ) ^ 2 * s)
      = (Nat.gcd q q' : ℝ) ^ 2 * s := by
    norm_num
  have e4 : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ) ^ 2
      * ((Nat.gcd q q' : ℝ) ^ 2 * s) = (Nat.lcm q q' : ℝ) ^ 2 * s := by
    have hab : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ)
        = (Nat.lcm q q' : ℝ) / (Nat.gcd q q' : ℝ) := by
      rw [Nat.cast_mul, haR, hbR, div_mul_div_comm,
        div_eq_div_iff (by positivity) hgR.ne']
      linear_combination (-(Nat.gcd q q' : ℝ)) * hglqq
    rw [hab, div_pow]
    field_simp
  unfold fieldDefect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco,
    e1, e2, e3, e4]

/-- **The defect annihilates affine log weights**: if a reflection
sends `log Z′(π²/α)` to `log Z(α)` plus an affine weight
`a·log α + b`, the weight cancels in the four-term alternating sum
— the constant by sign count zero, the log-linear part by
`gcd·lcm = q·q′` — and the field defect reflects with no weight at
all. -/
theorem fieldDefect_dual_of_log_reflect {Z Z' : ℝ → ℝ} {a b : ℝ}
    (hrefl : ∀ α : ℝ, 0 < α →
      Real.log (Z' (Real.pi ^ 2 / α))
        = a * Real.log α + b + Real.log (Z α))
    {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect Z s q q'
      = fieldDefect Z' (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  -- arithmetic of the reduction
  have hg : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hq
  have hgq : Nat.gcd q q' ∣ q := Nat.gcd_dvd_left q q'
  have hgq' : Nat.gcd q q' ∣ q' := Nat.gcd_dvd_right q q'
  have hco : Nat.Coprime (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
    Nat.coprime_div_gcd_div_gcd hg
  -- real casts
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hg
  have hlR : (0 : ℝ) < (Nat.lcm q q' : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq.ne' hq'.ne')
  have hglqq : (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)
      = (q : ℝ) * (q' : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm q q'
  have haR : ((q / Nat.gcd q q' : ℕ) : ℝ)
      = (q : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq hgR.ne'
  have hbR : ((q' / Nat.gcd q q' : ℕ) : ℝ)
      = (q' : ℝ) / (Nat.gcd q q' : ℝ) := Nat.cast_div hgq' hgR.ne'
  set t : ℝ := Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s) with htdef
  -- the involution permutes the four couplings
  have hswap : ∀ x y : ℝ, 0 < x → 0 < y
      → x * y = (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)
      → (x / (Nat.gcd q q' : ℝ)) ^ 2 * t
        = Real.pi ^ 2 / (y ^ 2 * s) := by
    intro x y hx hy hxy
    have hgl : (Nat.gcd q q' : ℝ) ^ 2 * ((Nat.lcm q q' : ℝ) ^ 2 * s)
        = x ^ 2 * (y ^ 2 * s) := by
      calc (Nat.gcd q q' : ℝ) ^ 2 * ((Nat.lcm q q' : ℝ) ^ 2 * s)
          = ((Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ)) ^ 2 * s := by ring
        _ = (x * y) ^ 2 * s := by rw [hxy]
        _ = x ^ 2 * (y ^ 2 * s) := by ring
    rw [htdef, div_pow, div_mul_div_comm, hgl,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e1 : ((q / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((q' : ℝ) ^ 2 * s) := by
    rw [haR]
    exact hswap _ _ hqR hq'R (by linarith [hglqq])
  have e2 : ((q' / Nat.gcd q q' : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((q : ℝ) ^ 2 * s) := by
    rw [hbR]
    exact hswap _ _ hq'R hqR (by linarith [hglqq])
  have e3 : ((1 : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s) := by
    rw [htdef]
    norm_num
  have e4 : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ) ^ 2 * t
      = Real.pi ^ 2 / ((Nat.gcd q q' : ℝ) ^ 2 * s) := by
    have hab : (((q / Nat.gcd q q') * (q' / Nat.gcd q q') : ℕ) : ℝ)
        = (Nat.lcm q q' : ℝ) / (Nat.gcd q q' : ℝ) := by
      rw [Nat.cast_mul, haR, hbR, div_mul_div_comm,
        div_eq_div_iff (by positivity) hgR.ne']
      linear_combination (-(Nat.gcd q q' : ℝ)) * hglqq
    rw [hab, htdef, div_pow, div_mul_div_comm,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- the four dual terms, reflected back through the affine weight
  have hda := hrefl ((q' : ℝ) ^ 2 * s) (by positivity)
  have hdb := hrefl ((q : ℝ) ^ 2 * s) (by positivity)
  have hdg := hrefl ((Nat.lcm q q' : ℝ) ^ 2 * s) (by positivity)
  have hdl := hrefl ((Nat.gcd q q' : ℝ) ^ 2 * s) (by positivity)
  -- the log-linear weights cancel by `gcd·lcm = q·q′`
  have hlogsum : Real.log ((q : ℝ) ^ 2 * s) + Real.log ((q' : ℝ) ^ 2 * s)
      = Real.log ((Nat.gcd q q' : ℝ) ^ 2 * s)
        + Real.log ((Nat.lcm q q' : ℝ) ^ 2 * s) := by
    rw [Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne',
      Real.log_mul (by positivity) hs.ne']
    have hsq : Real.log ((q : ℝ) ^ 2) + Real.log ((q' : ℝ) ^ 2)
        = Real.log ((Nat.gcd q q' : ℝ) ^ 2)
          + Real.log ((Nat.lcm q q' : ℝ) ^ 2) := by
      rw [← Real.log_mul (by positivity) (by positivity),
        ← Real.log_mul (by positivity) (by positivity)]
      congr 1
      linear_combination
        (-((q : ℝ) * (q' : ℝ)
          + (Nat.gcd q q' : ℝ) * (Nat.lcm q q' : ℝ))) * hglqq
    linarith
  unfold fieldDefect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco,
    e1, e2, e3, e4, hda, hdb, hdg, hdl]
  linear_combination (-a) * hlogsum

end Theaetetus
