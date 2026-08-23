import Theaetetus.Correlation

/-! # The equality cases of the correlation inequalities

The correlation proof passes through two analytic inequalities on
the parity feature vectors: Cauchy–Schwarz pairing
`parityVector M α (x + y)` against `parityVector M α (x - y)`, and
the arithmetic–geometric mean that turns the resulting product
bound into the averaged reflection bound. This module characterizes
equality in both. They are biconditionals: equality is named, not
merely exploited.

The criterion is proved first without Gaussian masses. For strictly
positive finite vectors the squared pairing meets the product of
the squared norms exactly when one vector is a positive multiple of
the other (`sum_mul_sq_eq_sq_mul_sq_iff_of_pos`), by the Lagrange
identity: the sum of squares
`∑ (f i·‖g‖² − g i·⟪f, g⟫)²` equals `‖g‖²·(‖f‖²·‖g‖² − ⟪f, g⟫²)`,
so equality forces every coordinate to satisfy
`f i·‖g‖² = g i·⟪f, g⟫`. Strict positivity is what removes the
zero-vector exceptions of the general equality case and forces the
ratio `⟪f, g⟫/‖g‖²` to be positive.

Transported through the two identities of the parity geometry — the
product identity `gramMass_mul_eq_inner` and the norm identity
`sum_sq_parityVector` — this reads:

    m(x)²·m(y)² = m(0)²·m(x+y)·m(x−y)

exactly when the two feature vectors are positively collinear
(`ParityCollinear`, `gramMass_sq_mul_sq_eq_iff`), and

    m(x)·m(y) = m(0)·(m(x+y) + m(x−y))/2

exactly when they are positively collinear *and* the two reflected
masses agree (`gramMass_mul_eq_avg_iff`). Those two conditions
collapse: they hold exactly when the two feature vectors are
literally equal (`gramMass_mul_eq_avg_iff_parityVector_eq`), since
equal reflected masses make the squared norms agree and force the
positive multiplier to be `1`. That vector equality is the form the
equality chain consumes; the conjunction keeps the two links
visible one at a time. In the forward direction
of the second both inequalities of the chain must saturate, and
positivity of the base mass is what forces it: the averaged
equality squared against the product bound leaves
`m(0)²·(m(x+y) − m(x−y))² ≤ 0`, hence the arithmetic–geometric
equality `m(x+y) = m(x−y)`, and with it the product bound becomes
an equality too.

These are the analytic links of the zero-defect equality chain. The
remaining links are arithmetic: saturation of every residue-class
inequality in `gramMass_dilate_mul_le` and
`gramMass_coprime_mul_le`, and the classification of the vanishing
locus of `QuadLatticeAction.defect` for scalar dilations. -/

namespace Theaetetus

open Matrix

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## Cauchy–Schwarz equality for strictly positive vectors -/

/-- **The Cauchy–Schwarz equality criterion** for strictly positive
finite vectors: the squared pairing equals the product of the
squared norms exactly when one vector is a positive multiple of the
other. The forward direction is the Lagrange identity in the form

    `∑ (f i · ‖g‖² − g i · ⟪f, g⟫)² = ‖g‖² · (‖f‖²·‖g‖² − ⟪f, g⟫²)`,

whose left side is a sum of squares, so equality forces every
coordinate ratio to be the constant `⟪f, g⟫ / ‖g‖²`. -/
theorem sum_mul_sq_eq_sq_mul_sq_iff_of_pos {ι : Type*} [Fintype ι]
    [Nonempty ι] {f g : ι → ℝ} (hf : ∀ i, 0 < f i) (hg : ∀ i, 0 < g i) :
    (∑ i, f i * g i) ^ 2 = (∑ i, f i ^ 2) * (∑ i, g i ^ 2)
      ↔ ∃ r : ℝ, 0 < r ∧ ∀ i, f i = r * g i := by
  have hSg : 0 < ∑ i, g i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (hg i) 2) Finset.univ_nonempty
  have hP : 0 < ∑ i, f i * g i :=
    Finset.sum_pos (fun i _ => mul_pos (hf i) (hg i)) Finset.univ_nonempty
  constructor
  · intro h
    have hzero : ∑ i, (f i * (∑ j, g j ^ 2) - g i * (∑ j, f j * g j)) ^ 2
        = 0 := by
      have hterm : ∀ i : ι,
          (f i * (∑ j, g j ^ 2) - g i * (∑ j, f j * g j)) ^ 2
            = (∑ j, g j ^ 2) ^ 2 * f i ^ 2
              - 2 * ((∑ j, g j ^ 2) * (∑ j, f j * g j)) * (f i * g i)
              + (∑ j, f j * g j) ^ 2 * g i ^ 2 := fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
      linear_combination (-(∑ j, g j ^ 2)) * h
    have hcoord : ∀ i : ι, f i * (∑ j, g j ^ 2) = g i * (∑ j, f j * g j) := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (f i * (∑ j, g j ^ 2)
          - g i * (∑ j, f j * g j)))).mp hzero i (Finset.mem_univ i)
      have hsub := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
      linarith
    refine ⟨(∑ j, f j * g j) / (∑ j, g j ^ 2), div_pos hP hSg, fun i => ?_⟩
    field_simp
    linarith [hcoord i]
  · rintro ⟨r, hr, hfg⟩
    have h1 : ∑ i, f i * g i = r * ∑ i, g i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hfg i]; ring
    have h2 : ∑ i, f i ^ 2 = r ^ 2 * ∑ i, g i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hfg i]; ring
    rw [h1, h2]
    ring

/-! ## Collinearity of the parity feature vectors -/

/-- **Parity collinearity**: the parity feature vectors at `u` and
`v` are positive multiples of one another. This is the geometric
content of equality in the correlation inequalities. -/
def ParityCollinear (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (u v : Fin d → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∀ c : Fin d → ZMod 2,
      parityVector M α u c = r * parityVector M α v c

/-! ## The two equality cases -/

/-- **The Cauchy–Schwarz link, characterized**: the correlation
inequality `m(x)²·m(y)² ≤ m(0)²·m(x+y)·m(x−y)` is an equality
exactly when the parity feature vectors at `x + y` and `x − y` are
positively collinear. -/
theorem gramMass_sq_mul_sq_eq_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x ^ 2 * gramMass M α y ^ 2
        = gramMass M α 0 ^ 2
            * (gramMass M α (x + y) * gramMass M α (x - y))
      ↔ ParityCollinear M α (x + y) (x - y) := by
  have key := sum_mul_sq_eq_sq_mul_sq_iff_of_pos
    (f := parityVector M α (x + y)) (g := parityVector M α (x - y))
    (parityVector_pos hM hα (x + y)) (parityVector_pos hM hα (x - y))
  rw [sum_sq_parityVector hM hα (x + y), sum_sq_parityVector hM hα (x - y),
    ← gramMass_mul_eq_inner hM hα x y] at key
  refine Iff.trans ?_ key
  constructor <;> intro h <;> linear_combination h

/-- **The averaged link, characterized**: the reflection bound
`m(x)·m(y) ≤ m(0)·(m(x+y) + m(x−y))/2` is an equality exactly when
the parity feature vectors at `x + y` and `x − y` are positively
collinear *and* the two reflected masses agree — Cauchy–Schwarz
saturated together with the arithmetic–geometric mean. -/
theorem gramMass_mul_eq_avg_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
        = gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)
      ↔ ParityCollinear M α (x + y) (x - y)
          ∧ gramMass M α (x + y) = gramMass M α (x - y) := by
  have h0 : 0 < gramMass M α 0 := gramMass_pos hM hα 0
  have hx : 0 < gramMass M α x := gramMass_pos hM hα x
  have hy : 0 < gramMass M α y := gramMass_pos hM hα y
  have hp : 0 < gramMass M α (x + y) := gramMass_pos hM hα (x + y)
  have hm : 0 < gramMass M α (x - y) := gramMass_pos hM hα (x - y)
  constructor
  · intro h
    have hsq : gramMass M α x ^ 2 * gramMass M α y ^ 2
        = gramMass M α 0 ^ 2
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2) ^ 2 := by
      linear_combination
        (gramMass M α x * gramMass M α y
          + gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)) * h
    have hT := gramMass_sq_mul_sq_le hM hα x y
    have hgap : gramMass M α 0 ^ 2
        * (gramMass M α (x + y) - gramMass M α (x - y)) ^ 2 ≤ 0 := by
      nlinarith [hT, hsq]
    have hdiff : (gramMass M α (x + y) - gramMass M α (x - y)) ^ 2 = 0 := by
      refine le_antisymm ?_ (sq_nonneg _)
      nlinarith [hgap, pow_pos h0 2,
        sq_nonneg (gramMass M α (x + y) - gramMass M α (x - y))]
    have hab : gramMass M α (x + y) = gramMass M α (x - y) := by
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hdiff
      linarith
    refine ⟨(gramMass_sq_mul_sq_eq_iff hM hα x y).mp ?_, hab⟩
    rw [hsq, hab]
    ring
  · rintro ⟨hcol, hab⟩
    have hcs := (gramMass_sq_mul_sq_eq_iff hM hα x y).mpr hcol
    have hsq : (gramMass M α x * gramMass M α y) ^ 2
        = (gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)) ^ 2 := by
      rw [hab] at hcs ⊢
      linear_combination hcs
    exact (pow_left_inj₀ (mul_pos hx hy).le
      (mul_nonneg h0.le (by positivity)) two_ne_zero).mp hsq

/-- **The averaged equality, canonically**: the reflection bound is
an equality exactly when the two parity feature vectors are equal.
Collinearity with a positive multiplier and equal reflected masses
force the multiplier to be `1`, since the squared norms are the two
reflected masses scaled by the same positive base mass. This is the
form the equality chain consumes; the two links stay visible
separately in `gramMass_mul_eq_avg_iff`. -/
theorem gramMass_mul_eq_avg_iff_parityVector_eq (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
        = gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)
      ↔ parityVector M α (x + y) = parityVector M α (x - y) := by
  have h0 : 0 < gramMass M α 0 := gramMass_pos hM hα 0
  have hnp := sum_sq_parityVector hM hα (x + y)
  have hnm := sum_sq_parityVector hM hα (x - y)
  rw [gramMass_mul_eq_avg_iff hM hα]
  constructor
  · rintro ⟨⟨r, hr, hfg⟩, hab⟩
    have hgpos :
        0 < ∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2 := by
      rw [hnm]
      exact mul_pos h0 (gramMass_pos hM hα _)
    have hsum : (∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2)
        = r ^ 2 * ∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2 :=
      calc (∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2)
          = ∑ c : Fin d → ZMod 2, parityVector M α (x + y) c ^ 2 := by
            rw [hnp, hnm, hab]
        _ = r ^ 2 * ∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by rw [hfg c]; ring
    have hr2 : (r - 1) * (r + 1) = 0 := by
      have hfac : (r ^ 2 - 1)
          * (∑ c : Fin d → ZMod 2, parityVector M α (x - y) c ^ 2) = 0 := by
        linear_combination -hsum
      rcases mul_eq_zero.mp hfac with h2 | h2
      · linear_combination h2
      · exact absurd h2 hgpos.ne'
    have hr1 : r = 1 := by
      rcases mul_eq_zero.mp hr2 with h2 | h2 <;> linarith
    funext c
    rw [hfg c, hr1, one_mul]
  · intro h
    have hab : gramMass M α (x + y) = gramMass M α (x - y) :=
      mul_left_cancel₀ h0.ne' (by rw [← hnp, ← hnm, h])
    exact ⟨⟨1, one_pos, fun c => by rw [h, one_mul]⟩, hab⟩

end Theaetetus
