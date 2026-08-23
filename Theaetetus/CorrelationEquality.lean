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

These are the analytic links of the zero-defect equality chain.
The next link is arithmetic, and it reduces to them. Both sides of
scalar dilation monotonicity are sums over residue classes of the
same averaged bound, at the named shifts `dilateShift n x` and
`residueShift n c` (`gramMass_dilate_mul_eq_sum`,
`gramMass_dilate_avg_eq_sum`). A sum of dominated terms meets its
dominating sum exactly when every term does (`sum_eq_iff_of_le`),
so the global equality is exactly class-by-class saturation, and
each saturated class is exactly a reflection-invariant feature
vector: `gramMass_dilate_mul_eq_iff` says that scalar dilation is
an equality precisely when `parityVector` at `u + v_c` equals
`parityVector` at `u − v_c` for every residue class `c`.

The coprime resummation closes the same way, one grid further out.
Both sides of positive correlation at coprime dilations decompose
over the `b`-grid into the two sides of scalar dilation
monotonicity at dilation `a`, taken at the outer shifts
`dilatedResidueShift a b r` (`gramMass_coprime_mul_eq_sum` and
`gramMass_coprime_avg_eq_sum`, the second through the unit
permutation `r ↦ a·r` of residues,
`sum_gramMass_dilatedResidueShift`). Saturation is therefore class
by class (`gramMass_coprime_mul_eq_iff_forall_class`), and since
the outer shift normalizes,
`dilateShift a (dilatedResidueShift a b r) = residueShift b r`,
each outer class contributes the residue family of its own
dilation. The criterion is two-grid
(`gramMass_coprime_mul_eq_iff`): correlation at coprime dilations
is an equality exactly when

    parityVector (v_r + v_c) = parityVector (v_r − v_c)

at the joint scale, for every residue `r` mod `b` and every residue
`c` mod `a` — every point of the `b`-grid a reflection center for
the `a`-grid.

The chain closes at the defect itself. For a positive field the
defect at a coprime pair vanishes exactly when the partition values
multiply across the rectangle `{a, b, 1, a·b}`
(`fieldDefect_eq_zero_iff_mul_eq`, generic and logarithm-only), so
in the Gram chart a vanishing defect is exactly that mass identity
(`gramDefect_eq_zero_iff_mul_eq`) and hence exactly the two-grid
criterion (`TwoGridReflection`,
`gramDefect_eq_zero_iff_twoGridReflection`). Intrinsically, the
defect of a positive-definite lattice action vanishes at a coprime
pair exactly when the criterion holds in a chosen integral chart
(`QuadLatticeAction.defect_eq_zero_iff_twoGridReflection`); the
left side of that equivalence names no chart, so the criterion
holds in one integral chart exactly when it holds in every other
(`QuadLatticeAction.twoGridReflection_gram_iff`) — chart
independence with no coordinate change between parity vectors.

What remains is one rigidity statement: in positive rank, for
coprime `a, b > 1`, the two-grid reflection condition is
impossible. With it, `fieldDefect_div_gcd` reduces an arbitrary
pair to its coprime base and turns the equivalence into the
classification of the vanishing locus. -/

namespace Theaetetus

open Matrix

universe u

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

/-! ## Saturation of the residue-class decomposition -/

/-- **Finite-sum saturation**: a sum of dominated terms meets its
dominating sum exactly when every term does. -/
theorem sum_eq_iff_of_le {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (h : ∀ i, f i ≤ g i) :
    (∑ i, f i) = ∑ i, g i ↔ ∀ i, f i = g i := by
  rw [Finset.sum_eq_sum_iff_of_le fun i _ => h i]
  exact ⟨fun hh i => hh i (Finset.mem_univ i), fun hh i _ => hh i⟩

/-- **The scalar-dilation link, characterized**: monotonicity under
scalar dilation is an equality exactly when every residue class is
reflection-invariant — the parity feature vector at
`u + v_c` equal to the one at `u − v_c`, class by class. Both sides
decompose over residue classes, so the global equality saturates
every class of the averaged reflection bound, and each saturated
class is exactly a reflection-invariant feature vector. -/
theorem gramMass_dilate_mul_eq_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
        = gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x
      ↔ ∀ c : Fin d → ZMod n,
          parityVector M ((n : ℝ) ^ 2 * α)
              (dilateShift n x + residueShift n c)
            = parityVector M ((n : ℝ) ^ 2 * α)
                (dilateShift n x - residueShift n c) := by
  have hβ : (0 : ℝ) < (n : ℝ) ^ 2 * α := by
    have hn : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  rw [gramMass_dilate_mul_eq_sum hM hα x n,
    gramMass_dilate_avg_eq_sum hM hα x n,
    sum_eq_iff_of_le fun c => gramMass_mul_le_avg hM hβ (dilateShift n x)
      (residueShift n c)]
  exact forall_congr' fun c =>
    gramMass_mul_eq_avg_iff_parityVector_eq hM hβ (dilateShift n x)
      (residueShift n c)

/-! ## Saturation of the coprime resummation -/

/-- **The coprime link, class by class**: positive correlation at
coprime dilations is an equality exactly when every outer residue
class saturates scalar dilation monotonicity. Both sides decompose
over the `b`-grid, so the global equality is class-by-class
saturation and nothing else. -/
theorem gramMass_coprime_mul_eq_iff_forall_class (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
        = gramMass M s 0
            * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      ↔ ∀ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
                (dilateShift a (dilatedResidueShift a b r))
              * gramMass M ((b : ℝ) ^ 2 * s) 0
            = gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
                * gramMass M ((b : ℝ) ^ 2 * s)
                    (dilatedResidueShift a b r) := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hβb : (0 : ℝ) < (b : ℝ) ^ 2 * s := by positivity
  rw [gramMass_coprime_mul_eq_sum hM hs ha,
    gramMass_coprime_avg_eq_sum hM hs hco,
    sum_eq_iff_of_le fun r =>
      gramMass_dilate_mul_le hM hβb (dilatedResidueShift a b r) a]

/-- **The two-grid reflection criterion**: positive correlation at
coprime dilations is an equality exactly when every point of the
`b`-grid is a center of reflection for the `a`-grid, in the parity
feature vectors at the joint scale. Each outer class contributes the
inner residue family of its own dilation, and the outer shift
normalizes to the residue shift of the `b`-grid. -/
theorem gramMass_coprime_mul_eq_iff (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
        = gramMass M s 0
            * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      ↔ ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a),
          parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
              (residueShift b r + residueShift a c)
            = parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
                (residueShift b r - residueShift a c) := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hβb : (0 : ℝ) < (b : ℝ) ^ 2 * s := by positivity
  rw [gramMass_coprime_mul_eq_iff_forall_class hM hs ha hb hco]
  refine forall_congr' fun r => ?_
  rw [gramMass_dilate_mul_eq_iff hM hβb (dilatedResidueShift a b r) a,
    dilateShift_dilatedResidueShift ha b r]

/-! ## From a vanishing defect to the two-grid symmetry -/

/-- **The two-grid reflection criterion** at coprime dilations `a`
and `b`: at the joint scale every point of the `b`-grid is a center
of reflection for the `a`-grid, read in the parity feature
vectors. -/
def TwoGridReflection (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (a b : ℕ) : Prop :=
  ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a),
    parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
        (residueShift b r + residueShift a c)
      = parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
          (residueShift b r - residueShift a c)

/-- **The Gram mass bridge**: at a coprime pair the Gram defect
vanishes exactly when the Boltzmann masses multiply across the
resolution rectangle, whose corners are `{a, b, 1, a·b}`. -/
theorem gramDefect_eq_zero_iff_mul_eq (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    gramDefect M s a b = 0
      ↔ gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
          = gramMass M s 0
              * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0 := by
  have e2 : ((a * b : ℕ) : ℝ) ^ 2 * s = (a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s) := by
    push_cast
    ring
  rw [gramDefect_eq_fieldDefect,
    fieldDefect_eq_zero_iff_mul_eq (fun β hβ => gramTheta_pos hM hβ) hs ha hb
      hco, e2]
  simp only [gramMass_zero]

/-- **The coprime zero-defect/two-grid equivalence** in the Gram
chart: the defect of a positive-definite Gram form vanishes at a
coprime pair exactly when the two-grid reflection criterion holds at
the joint scale. -/
theorem gramDefect_eq_zero_iff_twoGridReflection (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramDefect M s a b = 0 ↔ TwoGridReflection M s a b :=
  (gramDefect_eq_zero_iff_mul_eq hM hs ha hb hco).trans
    (gramMass_coprime_mul_eq_iff hM hs ha hb hco)

/-- **The criterion is symmetric in the pair**: swapping the two
dilations preserves it, because both readings are the vanishing of
the same defect and the defect is symmetric in its resolutions. -/
theorem twoGridReflection_comm (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    TwoGridReflection M s a b ↔ TwoGridReflection M s b a := by
  rw [← gramDefect_eq_zero_iff_twoGridReflection hM hs ha hb hco,
    ← gramDefect_eq_zero_iff_twoGridReflection hM hs hb ha hco.symm,
    gramDefect_eq_fieldDefect, gramDefect_eq_fieldDefect,
    fieldDefect_comm]

/-- **The intrinsic equivalence**: the defect of a positive-definite
lattice action vanishes at a coprime pair exactly when the two-grid
reflection criterion holds in one — hence any — integral chart. -/
theorem QuadLatticeAction.defect_eq_zero_iff_twoGridReflection
    (Q : QuadLatticeAction.{u}) {n : ℕ} (bs : Module.Basis (Fin n) ℤ Q.Λ)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    Q.defect s a b = 0 ↔ TwoGridReflection (Q.gram bs) s a b := by
  rw [Q.defect_eq_gramDefect bs]
  exact gramDefect_eq_zero_iff_twoGridReflection (Q.gram_posDef bs) hs ha hb
    hco

/-- **Chart independence of the criterion**: the two-grid condition
holds in one integral chart exactly when it holds in every other,
both being equivalent to the same intrinsic vanishing. No change of
coordinates between the parity vectors is computed. -/
theorem QuadLatticeAction.twoGridReflection_gram_iff
    (Q : QuadLatticeAction.{u}) {n m : ℕ} (bs : Module.Basis (Fin n) ℤ Q.Λ)
    (bs' : Module.Basis (Fin m) ℤ Q.Λ) {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    TwoGridReflection (Q.gram bs) s a b
      ↔ TwoGridReflection (Q.gram bs') s a b :=
  (Q.defect_eq_zero_iff_twoGridReflection bs hs ha hb hco).symm.trans
    (Q.defect_eq_zero_iff_twoGridReflection bs' hs ha hb hco)

end Theaetetus
