import Theaetetus.ShiftedMass
import Theaetetus.LatticeDuality

/-! # Positive correlation and the sign of the defect

The Regev–Stephens-Davidowitz port. The proof's real content is a
finite Hilbert-space geometry: the **parity feature vector**
`parityVector M α z`, indexed by the parity classes, whose entries
are half-shifted masses at doubled coupling. Two public identities
carry everything: the product of two shifted masses is the inner
product of feature vectors at the shift sum and difference
(`gramMass_mul_eq_inner`), and the squared norm of a feature
vector is a mass product (`sum_sq_parityVector`). Cauchy–Schwarz
then gives the correlation inequality
`m(x)²m(y)² ≤ m(0)²·m(x+y)·m(x−y)` (`gramMass_sq_mul_sq_le`), its
averaged form (`gramMass_mul_le_avg`), monotonicity under scalar
dilation — the scalar-dilation specialization of sublattice
monotonicity (`gramMass_dilate_mul_le`) — and positive correlation
at coprime dilations (`gramMass_coprime_mul_le`).

The landing is the sign: the Gram defect of every positive-definite
form is nonpositive at every scale and pair of resolutions
(`gramDefect_nonpos`), and so is the intrinsic defect of every
positive-definite lattice action
(`QuadLatticeAction.defect_nonpos`). The defect is logarithmic
correlation slack whose sign is controlled by the parity-vector
Cauchy–Schwarz geometry; an equality analysis must track
collinearity of the feature vectors, the AM–GM equality, and the
saturation of every residue-class inequality in the chain. The
first two are characterized in `Theaetetus.CorrelationEquality`. -/

namespace Theaetetus

open Matrix

universe u

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## The parity feature vector -/

/-- **The parity feature vector**: the coset-mass vector of the
parity classes — each entry the mass of a half-shifted parity coset
at doubled coupling. -/
noncomputable def parityVector (M : Matrix (Fin d) (Fin d) ℝ)
    (α : ℝ) (z : Fin d → ℝ) (c : Fin d → ZMod 2) : ℝ :=
  gramMass M (2 * α) ((2 : ℝ)⁻¹ • (z + fun i => ((c i).val : ℝ)))

theorem parityVector_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (z : Fin d → ℝ) (c : Fin d → ZMod 2) :
    0 < parityVector M α z c :=
  gramMass_pos hM (by linarith) _

/-- **The product identity**: the product of two shifted masses is
the inner product of the parity feature vectors at the shift sum
and difference. -/
theorem gramMass_mul_eq_inner (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      = ∑ c : Fin d → ZMod 2,
          parityVector M α (x + y) c * parityVector M α (x - y) c :=
  gramMass_mul_gramMass hM hα x y

/-- **The norm identity**: the squared norm of a parity feature
vector is a mass product — the product identity at difference
zero. -/
theorem sum_sq_parityVector (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (z : Fin d → ℝ) :
    ∑ c : Fin d → ZMod 2, parityVector M α z c ^ 2
      = gramMass M α 0 * gramMass M α z := by
  have h := gramMass_mul_gramMass hM hα z 0
  rw [add_zero, sub_zero] at h
  calc ∑ c : Fin d → ZMod 2, parityVector M α z c ^ 2
      = ∑ c : Fin d → ZMod 2,
          parityVector M α z c * parityVector M α z c :=
        Finset.sum_congr rfl fun c _ => pow_two _
    _ = gramMass M α z * gramMass M α 0 := h.symm
    _ = gramMass M α 0 * gramMass M α z := mul_comm _ _

/-! ## The correlation inequalities -/

/-- **The Regev–Stephens-Davidowitz inequality** at the Gram chart:
`m(x)²·m(y)² ≤ m(0)²·m(x+y)·m(x−y)` — Cauchy–Schwarz on the parity
feature vectors, with both norms evaluated by the norm identity. -/
theorem gramMass_sq_mul_sq_le (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x ^ 2 * gramMass M α y ^ 2
      ≤ gramMass M α 0 ^ 2
          * (gramMass M α (x + y) * gramMass M α (x - y)) := by
  have h1 := gramMass_mul_eq_inner hM hα x y
  have h2 := sum_sq_parityVector hM hα (x + y)
  have h3 := sum_sq_parityVector hM hα (x - y)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (parityVector M α (x + y)) (parityVector M α (x - y))
  rw [← h1, h2, h3] at hcs
  calc gramMass M α x ^ 2 * gramMass M α y ^ 2
      = (gramMass M α x * gramMass M α y) ^ 2 := by ring
    _ ≤ gramMass M α 0 * gramMass M α (x + y)
          * (gramMass M α 0 * gramMass M α (x - y)) := hcs
    _ = gramMass M α 0 ^ 2
          * (gramMass M α (x + y) * gramMass M α (x - y)) := by ring

/-- The averaged reflection bound:
`m(x)·m(y) ≤ m(0)·(m(x+y) + m(x−y))/2`. -/
theorem gramMass_mul_le_avg (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      ≤ gramMass M α 0
          * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2) := by
  have hT := gramMass_sq_mul_sq_le hM hα x y
  have h0 := (gramMass_pos hM hα 0).le
  have hp := (gramMass_pos hM hα (x + y)).le
  have hm := (gramMass_pos hM hα (x - y)).le
  have hsq : (gramMass M α x * gramMass M α y) ^ 2
      ≤ (gramMass M α 0
          * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)) ^ 2 := by
    nlinarith [sq_nonneg (gramMass M α (x + y) - gramMass M α (x - y)),
      sq_nonneg (gramMass M α 0), hT]
  exact le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg h0 (div_nonneg (add_nonneg hp hm) (by norm_num))) hsq

/-- Argument congruence for the shifted mass. -/
private theorem gramMass_congr {α α' : ℝ} {x x' : Fin d → ℝ}
    (hα : α = α') (hx : x = x') :
    gramMass M α x = gramMass M α' x' := by
  rw [hα, hx]

/-! ## The residue-class decomposition of a scalar dilation -/

/-- The dilated shift `u = n⁻¹·x`: the base point of the
residue-class decomposition at dilation `n`. -/
noncomputable def dilateShift (n : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  (n : ℝ)⁻¹ • x

/-- The residue shift `v_c = n⁻¹·c` at the residue class `c`,
through the canonical real lift of a residue vector. -/
noncomputable def residueShift (n : ℕ) (c : Fin d → ZMod n) : Fin d → ℝ :=
  (n : ℝ)⁻¹ • (fun i => ((c i).val : ℝ))

theorem dilateShift_eq (n : ℕ) (x : Fin d → ℝ) :
    dilateShift n x = (n : ℝ)⁻¹ • x :=
  rfl

theorem residueShift_eq (n : ℕ) (c : Fin d → ZMod n) :
    residueShift n c = (n : ℝ)⁻¹ • (fun i => ((c i).val : ℝ)) :=
  rfl

/-- **The dilated pairing, decomposed**: the left side of scalar
dilation monotonicity is the sum over residue classes of the pairing
of the dilated shift against the residue shift — the coset
decomposition of the full-lattice mass at the trivial shift. -/
theorem gramMass_dilate_mul_eq_sum (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x)
            * gramMass M ((n : ℝ) ^ 2 * α) (residueShift n c) := by
  rw [gramMass_coset hM hα (0 : Fin d → ℝ) n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine congrArg _ (gramMass_congr rfl ?_)
  funext i
  show (n : ℝ)⁻¹ * (0 + ((c i).val : ℝ)) = (n : ℝ)⁻¹ * ((c i).val : ℝ)
  ring

/-- **The aligned pairing, decomposed**: the right side of scalar
dilation monotonicity is the sum over residue classes of the
averaged reflection of the dilated shift by the residue shift. Both
halves re-sum to the same full-lattice mass, the minus half by
evenness. -/
theorem gramMass_dilate_avg_eq_sum (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α) 0
            * ((gramMass M ((n : ℝ) ^ 2 * α)
                  (dilateShift n x + residueShift n c)
                + gramMass M ((n : ℝ) ^ 2 * α)
                  (dilateShift n x - residueShift n c)) / 2) := by
  have hplus : ∑ c : Fin d → ZMod n,
      gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x + residueShift n c)
      = gramMass M α x := by
    rw [gramMass_coset hM hα x n]
    exact Finset.sum_congr rfl fun c _ => gramMass_congr rfl (by
      funext i
      show (n : ℝ)⁻¹ * x i + (n : ℝ)⁻¹ * ((c i).val : ℝ)
          = (n : ℝ)⁻¹ * (x i + ((c i).val : ℝ))
      ring)
  have hminus : ∑ c : Fin d → ZMod n,
      gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x - residueShift n c)
      = gramMass M α x := by
    calc ∑ c : Fin d → ZMod n,
        gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x - residueShift n c)
        = ∑ c : Fin d → ZMod n,
            gramMass M ((n : ℝ) ^ 2 * α)
              (-((n : ℝ)⁻¹ • (-x + fun i => ((c i).val : ℝ)))) :=
          Finset.sum_congr rfl fun c _ => gramMass_congr rfl (by
            funext i
            show (n : ℝ)⁻¹ * x i - (n : ℝ)⁻¹ * ((c i).val : ℝ)
                = -((n : ℝ)⁻¹ * (-x i + ((c i).val : ℝ)))
            ring)
      _ = ∑ c : Fin d → ZMod n,
            gramMass M ((n : ℝ) ^ 2 * α)
              ((n : ℝ)⁻¹ • (-x + fun i => ((c i).val : ℝ))) :=
          Finset.sum_congr rfl fun c _ => gramMass_neg _ _
      _ = gramMass M α (-x) := (gramMass_coset hM hα (-x) n).symm
      _ = gramMass M α x := gramMass_neg α x
  rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
    hplus, hminus]
  congr 1
  ring

/-- **Monotonicity under scalar dilation** — the scalar-dilation
specialization of sublattice monotonicity: dilating the shifted
lattice by `n` against the full lattice mass is dominated by the
aligned pairing. Both sides decompose over residue classes, and the
averaged reflection bound holds in each class. -/
theorem gramMass_dilate_mul_le (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
      ≤ gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x := by
  have hβ : (0 : ℝ) < (n : ℝ) ^ 2 * α := by
    have hn : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  rw [gramMass_dilate_mul_eq_sum hM hα x n,
    gramMass_dilate_avg_eq_sum hM hα x n]
  exact Finset.sum_le_sum fun c _ => gramMass_mul_le_avg hM hβ _ _

/-! ## Positive correlation at coprime dilations -/

/-- The outer shift `x_r = a·(b⁻¹·r)`: the residue shift of the
`b`-grid, read in the chart dilated by `a`. -/
noncomputable def dilatedResidueShift (a b : ℕ) (r : Fin d → ZMod b) :
    Fin d → ℝ :=
  (a : ℝ) • residueShift b r

theorem dilatedResidueShift_eq (a b : ℕ) (r : Fin d → ZMod b) :
    dilatedResidueShift a b r = (a : ℝ) • residueShift b r :=
  rfl

/-- **Normalization**: dilating the outer shift by `a` returns the
residue shift of the `b`-grid. -/
theorem dilateShift_dilatedResidueShift {a : ℕ} (ha : 0 < a) (b : ℕ)
    (r : Fin d → ZMod b) :
    dilateShift a (dilatedResidueShift a b r) = residueShift b r := by
  have haR : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    exact this.ne'
  funext i
  show (a : ℝ)⁻¹ * ((a : ℝ) * ((b : ℝ)⁻¹ * ((r i).val : ℝ)))
      = (b : ℝ)⁻¹ * ((r i).val : ℝ)
  field_simp

/-- Multiplication by a unit is a bijection of residues. -/
private def zmodMulUnitEquiv {n : ℕ} (u : (ZMod n)ˣ) :
    ZMod n ≃ ZMod n where
  toFun z := u * z
  invFun z := (u⁻¹ : (ZMod n)ˣ) * z
  left_inv z := by
    show ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (((u : (ZMod n)ˣ) : ZMod n) * z) = z
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel u, Units.val_one,
      one_mul]
  right_inv z := by
    show ((u : (ZMod n)ˣ) : ZMod n) * (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * z) = z
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel u, Units.val_one,
      one_mul]

/-- Dilating a residue representative by `a` moves the shifted mass
to the representative of the dilated residue: the two shifts differ
by an integer vector. -/
private theorem gramMass_dilate_class {β : ℝ}
    {n : ℕ} [NeZero n] (a : ℕ) (r : Fin d → ZMod n) :
    gramMass M β ((n : ℝ)⁻¹ • fun i => ((a * (r i).val : ℕ) : ℝ))
      = gramMass M β
          ((n : ℝ)⁻¹ • fun i => ((((a : ZMod n) * r i)).val : ℝ)) := by
  have hdvd : ∀ i, (n : ℤ) ∣ ((a * (r i).val : ℕ) : ℤ)
      - ((((a : ZMod n) * r i)).val : ℤ) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_rightInverse (r i),
      ZMod.natCast_rightInverse ((a : ZMod n) * r i)]
    ring
  choose t ht using hdvd
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hvec : ((n : ℝ)⁻¹ • fun i => ((a * (r i).val : ℕ) : ℝ))
      = ((n : ℝ)⁻¹ • fun i => ((((a : ZMod n) * r i)).val : ℝ))
        + fun i => ((t i : ℤ) : ℝ) := by
    funext i
    have hz : ((a * (r i).val : ℕ) : ℤ)
        = ((((a : ZMod n) * r i)).val : ℤ) + n * t i := by
      linarith [ht i]
    have hr : ((a * (r i).val : ℕ) : ℝ)
        = ((((a : ZMod n) * r i)).val : ℝ) + (n : ℝ) * ((t i : ℤ) : ℝ) := by
      exact_mod_cast hz
    show (n : ℝ)⁻¹ * ((a * (r i).val : ℕ) : ℝ)
        = (n : ℝ)⁻¹ * ((((a : ZMod n) * r i)).val : ℝ) + ((t i : ℤ) : ℝ)
    rw [hr]
    field_simp
  rw [hvec, gramMass_int_shift]

/-- **The outer resummation**: the residue shifts of the `b`-grid,
dilated by `a`, run over the same `b`-grid — the unit `a mod b`
permutes the residues — so their masses re-sum to the mass of the
undilated lattice. -/
theorem sum_gramMass_dilatedResidueShift (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} [NeZero b] (hco : Nat.Coprime a b) :
    ∑ r : Fin d → ZMod b,
        gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r)
      = gramMass M s 0 := by
  set u : (ZMod b)ˣ := ZMod.unitOfCoprime a hco with hu
  have hcoe : ((u : ZMod b)) = (a : ZMod b) := ZMod.coe_unitOfCoprime a hco
  have hstep : ∀ r : Fin d → ZMod b,
      gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r)
      = gramMass M ((b : ℝ) ^ 2 * s)
          ((b : ℝ)⁻¹ • ((0 : Fin d → ℝ)
            + fun i => (((zmodMulUnitEquiv u (r i))).val : ℝ))) := by
    intro r
    have s1 : gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r)
        = gramMass M ((b : ℝ) ^ 2 * s)
          ((b : ℝ)⁻¹ • fun i => ((a * (r i).val : ℕ) : ℝ)) :=
      gramMass_congr rfl (by
        funext i
        show (a : ℝ) * ((b : ℝ)⁻¹ * ((r i).val : ℝ))
            = (b : ℝ)⁻¹ * ((a * (r i).val : ℕ) : ℝ)
        push_cast
        ring)
    have s2 : gramMass M ((b : ℝ) ^ 2 * s)
        ((b : ℝ)⁻¹ • fun i => ((a * (r i).val : ℕ) : ℝ))
        = gramMass M ((b : ℝ) ^ 2 * s)
          ((b : ℝ)⁻¹ • fun i => ((((a : ZMod b) * r i)).val : ℝ)) :=
      gramMass_dilate_class a r
    have s3 : gramMass M ((b : ℝ) ^ 2 * s)
        ((b : ℝ)⁻¹ • fun i => ((((a : ZMod b) * r i)).val : ℝ))
        = gramMass M ((b : ℝ) ^ 2 * s)
          ((b : ℝ)⁻¹ • ((0 : Fin d → ℝ)
            + fun i => (((zmodMulUnitEquiv u (r i))).val : ℝ))) :=
      gramMass_congr rfl (by
        funext i
        show (b : ℝ)⁻¹ * ((((a : ZMod b) * r i)).val : ℝ)
            = (b : ℝ)⁻¹ * (0 + (((u : ZMod b) * r i).val : ℝ))
        rw [hcoe]
        ring)
    exact (s1.trans s2).trans s3
  rw [Finset.sum_congr rfl fun r _ => hstep r]
  have hbij : ∑ r : Fin d → ZMod b,
      gramMass M ((b : ℝ) ^ 2 * s)
        ((b : ℝ)⁻¹ • ((0 : Fin d → ℝ)
          + fun i => (((zmodMulUnitEquiv u (r i))).val : ℝ)))
      = ∑ r : Fin d → ZMod b,
          gramMass M ((b : ℝ) ^ 2 * s)
            ((b : ℝ)⁻¹ • ((0 : Fin d → ℝ)
              + fun i => ((r i).val : ℝ))) :=
    Equiv.sum_comp (Equiv.piCongrRight fun _ => zmodMulUnitEquiv u)
      (fun r : Fin d → ZMod b =>
        gramMass M ((b : ℝ) ^ 2 * s)
          ((b : ℝ)⁻¹ • ((0 : Fin d → ℝ)
            + fun i => ((r i).val : ℝ))))
  rw [hbij, ← gramMass_coset hM hs (0 : Fin d → ℝ) b]

/-- **The correlation product, decomposed**: the left side of the
coprime bound is the sum over the `b`-grid of the left sides of
scalar dilation monotonicity at base scale `b²s`, dilation `a`, and
outer shift `x_r`. -/
theorem gramMass_coprime_mul_eq_sum (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) [NeZero b] :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
      = ∑ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
              (dilateShift a (dilatedResidueShift a b r))
            * gramMass M ((b : ℝ) ^ 2 * s) 0 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hβa : (0 : ℝ) < (a : ℝ) ^ 2 * s := by positivity
  rw [← Finset.sum_mul]
  congr 1
  rw [gramMass_coset hM hβa (0 : Fin d → ℝ) b]
  refine Finset.sum_congr rfl fun r _ => gramMass_congr (by ring) ?_
  funext i
  show (b : ℝ)⁻¹ * (0 + ((r i).val : ℝ))
      = (a : ℝ)⁻¹ * ((a : ℝ) * ((b : ℝ)⁻¹ * ((r i).val : ℝ)))
  field_simp
  ring

/-- **The aligned product, decomposed**: the right side of the
coprime bound is the sum over the `b`-grid of the right sides of
scalar dilation monotonicity at the same base scale, dilation, and
outer shifts — by the outer resummation. -/
theorem gramMass_coprime_avg_eq_sum (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} [NeZero b] (hco : Nat.Coprime a b) :
    gramMass M s 0 * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      = ∑ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
            * gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r) := by
  rw [← Finset.mul_sum, sum_gramMass_dilatedResidueShift hM hs hco]
  ring

/-- **Positive correlation at coprime dilations** — the
Regev–Stephens-Davidowitz correlation inequality at scalar
dilations of the integer lattice: for coprime `a`, `b`,

    `m_{a²s}(0)·m_{b²s}(0) ≤ m_s(0)·m_{a²b²s}(0)`.

Both sides decompose over the `b`-grid into the two sides of scalar
dilation monotonicity at dilation `a`, which holds in each outer
class. -/
theorem gramMass_coprime_mul_le (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
      ≤ gramMass M s 0
          * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0 := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hβb : (0 : ℝ) < (b : ℝ) ^ 2 * s := by positivity
  rw [gramMass_coprime_mul_eq_sum hM hs ha,
    gramMass_coprime_avg_eq_sum hM hs hco]
  exact Finset.sum_le_sum fun r _ =>
    gramMass_dilate_mul_le hM hβb (dilatedResidueShift a b r) a

/-! ## The sign of the defect -/

/-- **The sign of the Gram defect** — the Regev–Stephens-Davidowitz
implication at the Gram chart: every positive-definite Gram form
has nonpositive defect at every positive scale and every pair of
positive resolutions. -/
theorem gramDefect_nonpos (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    gramDefect M s q q' ≤ 0 := by
  rw [gramDefect_eq_fieldDefect, fieldDefect_div_gcd _ _ hq hq']
  have hg : 0 < Nat.gcd q q' := Nat.gcd_pos_of_pos_left _ hq
  have ha : 0 < q / Nat.gcd q q' :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q q')) hg
  have hb : 0 < q' / Nat.gcd q q' :=
    Nat.div_pos (Nat.le_of_dvd hq' (Nat.gcd_dvd_right q q')) hg
  have hco : Nat.Coprime (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
    Nat.coprime_div_gcd_div_gcd hg
  have hgR : (0 : ℝ) < (Nat.gcd q q' : ℝ) := by exact_mod_cast hg
  set t : ℝ := (Nat.gcd q q' : ℝ) ^ 2 * s with htdef
  have ht : (0 : ℝ) < t := by positivity
  set A := q / Nat.gcd q q'
  set B := q' / Nat.gcd q q'
  have haR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hb
  have hcorr := gramMass_coprime_mul_le hM ht ha hb hco
  simp only [gramMass_zero] at hcorr
  unfold fieldDefect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco]
  have hposA := gramTheta_pos hM (show (0:ℝ) < (A:ℝ)^2*t by positivity)
  have hposB := gramTheta_pos hM (show (0:ℝ) < (B:ℝ)^2*t by positivity)
  have hlog : Real.log (gramTheta M ((A:ℝ)^2*t) * gramTheta M ((B:ℝ)^2*t))
      ≤ Real.log (gramTheta M t
          * gramTheta M ((A:ℝ)^2*((B:ℝ)^2*t))) :=
    Real.log_le_log (mul_pos hposA hposB) hcorr
  rw [Real.log_mul hposA.ne' hposB.ne',
    Real.log_mul (gramTheta_pos hM ht).ne'
      (gramTheta_pos hM (show (0:ℝ) < (A:ℝ)^2*((B:ℝ)^2*t) by positivity)).ne']
    at hlog
  have e1 : ((1:ℕ):ℝ)^2 * t = t := by norm_num
  have e2 : ((A*B : ℕ):ℝ)^2 * t = (A:ℝ)^2*((B:ℝ)^2*t) := by
    push_cast
    ring
  rw [e1, e2]
  linarith [hlog]

/-- **The sign for every lattice** — Q1's inequality half, the
Regev–Stephens-Davidowitz implication: the intrinsic defect of
every positive-definite lattice action is nonpositive at every
positive scale and pair of positive resolutions. -/
theorem QuadLatticeAction.defect_nonpos (Q : QuadLatticeAction.{u})
    {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    Q.defect s q q' ≤ 0 := by
  rw [Q.defect_eq_gramDefect (Module.finBasis ℤ Q.Λ)]
  exact gramDefect_nonpos (Q.gram_posDef _) hs hq hq'

end Theaetetus
