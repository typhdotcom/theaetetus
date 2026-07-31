import Theaetetus.GramDuality
import Mathlib.Data.ZMod.Basic

/-! # The shifted Gaussian mass and its lattice decompositions

The α-scaled Gaussian mass of the shifted integer lattice,
`gramMass M α x = ∑_{k ∈ ℤᵈ} e^{−α·Q(x+k)}`, is the object the
correlation theory manipulates: sublattice and coset masses of
dilated lattices are shifted masses at rescaled coupling. This
module builds the object and its two decompositions:

* **residues** (`gramMass_coset`): splitting `ℤᵈ` by residues mod
  `n` writes the mass as a finite sum of masses of the `n`-dilated
  lattice, one per residue class;
* **parity pairs** (`gramMass_mul_gramMass`): the product of two
  shifted masses transports along `(k,m) ↦ (k+m, k−m)` — the
  Gaussian splits by the parallelogram law, the image splits by
  parity — into a finite sum, over parity classes, of products of
  half-shifted masses at doubled coupling.

Both decompositions rest on explicit integer bijections
(`zmodProdEquiv`, `parityPairEquiv`) taken coordinatewise. -/

namespace Theaetetus

open Matrix

/-! ## The integer bijections -/

/-- Every integer splits uniquely as a residue plus `n` times an
integer. -/
def zmodProdEquiv (n : ℕ) [NeZero n] : ZMod n × ℤ ≃ ℤ where
  toFun c := (c.1.val : ℤ) + n * c.2
  invFun j := ((j : ZMod n), (j - ((j : ZMod n).val : ℤ)) / n)
  left_inv := by
    rintro ⟨c, k⟩
    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hc : (((c.val : ℤ) + n * k : ℤ) : ZMod n) = c := by
      push_cast
      simp [ZMod.natCast_rightInverse c]
    refine Prod.ext hc ?_
    show ((c.val : ℤ) + n * k - ((((c.val : ℤ) + n * k : ℤ) : ZMod n).val : ℤ)) / n = k
    rw [hc]
    rw [show (c.val : ℤ) + n * k - (c.val : ℤ) = n * k from by ring]
    exact Int.mul_ediv_cancel_left k hn
  right_inv := by
    intro j
    have hval : (((j : ZMod n).val : ZMod n)) = (j : ZMod n) :=
      ZMod.natCast_rightInverse _
    have hdvd : (n : ℤ) ∣ (j - ((j : ZMod n).val : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hval]
      ring
    show ((j : ZMod n).val : ℤ) + n * ((j - ((j : ZMod n).val : ℤ)) / n) = j
    rw [Int.mul_ediv_cancel' hdvd]
    ring

@[simp] theorem zmodProdEquiv_apply (n : ℕ) [NeZero n] (c : ZMod n)
    (k : ℤ) : zmodProdEquiv n (c, k) = (c.val : ℤ) + n * k := rfl

/-- The parity-pair transform: `(c, p, q) ↦ (c + p + q, p − q)` is a
bijection from parity classes and integer pairs onto integer
pairs — the coordinatewise form of `T(z₁,z₂) = (z₁+z₂, z₁−z₂)`. -/
def parityPairEquiv : ZMod 2 × ℤ × ℤ ≃ ℤ × ℤ where
  toFun t := ((t.1.val : ℤ) + t.2.1 + t.2.2, t.2.1 - t.2.2)
  invFun km :=
    (((km.1 + km.2 : ℤ) : ZMod 2),
      (km.1 + km.2 - (((km.1 + km.2 : ℤ) : ZMod 2).val : ℤ)) / 2,
      (km.1 - km.2 - (((km.1 + km.2 : ℤ) : ZMod 2).val : ℤ)) / 2)
  left_inv := by
    rintro ⟨c, p, q⟩
    have hsum : ((c.val : ℤ) + p + q) + (p - q) = (c.val : ℤ) + 2 * p := by
      ring
    have hc : ((((c.val : ℤ) + p + q) + (p - q) : ℤ) : ZMod 2) = c := by
      rw [hsum]
      push_cast
      rw [show ((2 : ZMod 2)) = 0 from by decide]
      simp [ZMod.natCast_rightInverse c]
    refine Prod.ext hc (Prod.ext ?_ ?_)
    · show (((c.val : ℤ) + p + q) + (p - q)
          - (((((c.val : ℤ) + p + q) + (p - q) : ℤ) : ZMod 2).val : ℤ)) / 2 = p
      rw [hc, hsum]
      rw [show (c.val : ℤ) + 2 * p - (c.val : ℤ) = 2 * p from by ring]
      exact Int.mul_ediv_cancel_left p two_ne_zero
    · show (((c.val : ℤ) + p + q) - (p - q)
          - (((((c.val : ℤ) + p + q) + (p - q) : ℤ) : ZMod 2).val : ℤ)) / 2 = q
      rw [hc]
      rw [show ((c.val : ℤ) + p + q) - (p - q) - (c.val : ℤ) = 2 * q from
        by ring]
      exact Int.mul_ediv_cancel_left q two_ne_zero
  right_inv := by
    rintro ⟨k, m⟩
    have hval : ((((k + m : ℤ) : ZMod 2).val : ZMod 2))
        = ((k + m : ℤ) : ZMod 2) :=
      ZMod.natCast_rightInverse _
    have hdvd : (2 : ℤ) ∣ (k + m - (((k + m : ℤ) : ZMod 2).val : ℤ)) := by
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      push_cast at hval
      rw [hval]
      ring
    have hdvd' : (2 : ℤ) ∣ (k - m - (((k + m : ℤ) : ZMod 2).val : ℤ)) := by
      obtain ⟨t, ht⟩ := hdvd
      exact ⟨t - m, by omega⟩
    obtain ⟨t, ht⟩ := hdvd
    obtain ⟨t', ht'⟩ := hdvd'
    have hp : (k + m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2 = t := by
      rw [ht]
      exact Int.mul_ediv_cancel_left t two_ne_zero
    have hq : (k - m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2 = t' := by
      rw [ht']
      exact Int.mul_ediv_cancel_left t' two_ne_zero
    refine Prod.ext ?_ ?_
    · show ((((k + m : ℤ) : ZMod 2).val : ℤ)
          + (k + m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2
          + (k - m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2) = k
      rw [hp, hq]
      omega
    · show ((k + m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2
          - (k - m - (((k + m : ℤ) : ZMod 2).val : ℤ)) / 2) = m
      rw [hp, hq]
      omega

/-- The coordinatewise residue–quotient bijection on `ℤᵈ`. -/
def piZmodProdEquiv (n d : ℕ) [NeZero n] :
    (Fin d → ZMod n) × (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun ck i := zmodProdEquiv n (ck.1 i, ck.2 i)
  invFun j := (fun i => ((zmodProdEquiv n).symm (j i)).1,
    fun i => ((zmodProdEquiv n).symm (j i)).2)
  left_inv := by
    rintro ⟨c, k⟩
    have h : ∀ i, (zmodProdEquiv n).symm (zmodProdEquiv n (c i, k i))
        = (c i, k i) := fun i => Equiv.symm_apply_apply _ _
    exact Prod.ext (funext fun i => congrArg Prod.fst (h i))
      (funext fun i => congrArg Prod.snd (h i))
  right_inv := by
    intro j
    funext i
    exact (zmodProdEquiv n).apply_symm_apply (j i)

theorem piZmodProdEquiv_apply (n d : ℕ) [NeZero n]
    (c : Fin d → ZMod n) (k : Fin d → ℤ) (i : Fin d) :
    piZmodProdEquiv n d (c, k) i = ((c i).val : ℤ) + n * k i := rfl

/-- The coordinatewise parity-pair bijection on `ℤᵈ × ℤᵈ`. -/
def piParityEquiv (d : ℕ) :
    (Fin d → ZMod 2) × (Fin d → ℤ) × (Fin d → ℤ)
      ≃ (Fin d → ℤ) × (Fin d → ℤ) where
  toFun t := (fun i => (parityPairEquiv (t.1 i, t.2.1 i, t.2.2 i)).1,
    fun i => (parityPairEquiv (t.1 i, t.2.1 i, t.2.2 i)).2)
  invFun km := (fun i => (parityPairEquiv.symm (km.1 i, km.2 i)).1,
    fun i => (parityPairEquiv.symm (km.1 i, km.2 i)).2.1,
    fun i => (parityPairEquiv.symm (km.1 i, km.2 i)).2.2)
  left_inv := by
    rintro ⟨c, p, q⟩
    have h : ∀ i, parityPairEquiv.symm (parityPairEquiv (c i, p i, q i))
        = (c i, p i, q i) := fun i => Equiv.symm_apply_apply _ _
    exact Prod.ext (funext fun i => congrArg Prod.fst (h i))
      (Prod.ext (funext fun i => congrArg (fun z => z.2.1) (h i))
        (funext fun i => congrArg (fun z => z.2.2) (h i)))
  right_inv := by
    rintro ⟨k, m⟩
    have h : ∀ i, parityPairEquiv (parityPairEquiv.symm (k i, m i))
        = (k i, m i) := fun i => Equiv.apply_symm_apply _ _
    exact Prod.ext (funext fun i => congrArg Prod.fst (h i))
      (funext fun i => congrArg Prod.snd (h i))

theorem piParityEquiv_apply_fst (d : ℕ) (c : Fin d → ZMod 2)
    (p q : Fin d → ℤ) (i : Fin d) :
    (piParityEquiv d (c, p, q)).1 i = ((c i).val : ℤ) + p i + q i := rfl

theorem piParityEquiv_apply_snd (d : ℕ) (c : Fin d → ZMod 2)
    (p q : Fin d → ℤ) (i : Fin d) :
    (piParityEquiv d (c, p, q)).2 i = p i - q i := rfl

/-! ## The shifted mass -/

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- The α-scaled Gaussian mass of the shifted integer lattice:
`gramMass M α x = ∑_{k ∈ ℤᵈ} e^{−α·Q(x+k)}` where `Q` is the
quadratic form of `M`. At `x = 0` this is `gramTheta M α`
(`gramMass_zero`). -/
noncomputable def gramMass (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑' k : Fin d → ℤ,
    Real.exp (-α * ((x + fun i => (k i : ℝ))
      ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ))))

/-- Coordinatewise shift bound: `(t + z)² ≥ z²/2 − t²`. -/
private lemma sq_add_ge (t z : ℝ) : z ^ 2 / 2 - t ^ 2 ≤ (t + z) ^ 2 := by
  nlinarith [sq_nonneg (2 * t + z)]

/-- Summability of the shifted Boltzmann weight at every positive
coupling: coercivity dominates the translates by a product of
scalar Gaussians. -/
theorem summable_gramMass (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (-α * ((x + fun i => (k i : ℝ))
        ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ))))) := by
  obtain ⟨μ, hμ, hcoer⟩ := hM.exists_coercivity
  have hsum : Summable (fun k : Fin d → ℤ =>
      Real.exp (α * μ * ∑ i, x i ^ 2)
        * ∏ i, Real.exp (-(α * μ / 2) * (k i : ℝ) ^ 2)) :=
    (QuadraticAction.summable_finPi_prod d
      (fun _ z => Real.exp (-(α * μ / 2) * (z : ℝ) ^ 2))
      (fun _ z => (Real.exp_pos _).le)
      (fun _ => summable_theta _ (by positivity))).mul_left _
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => ?_) hsum
  have hQ : μ * ∑ i, (x i + (k i : ℝ)) ^ 2
      ≤ (x + fun i => (k i : ℝ)) ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ)) := by
    have := hcoer (x + fun i => (k i : ℝ))
    refine le_trans (le_of_eq ?_) this
    congr 1
  have hsq : ∑ i, ((k i : ℝ) ^ 2 / 2 - x i ^ 2)
      ≤ ∑ i, (x i + (k i : ℝ)) ^ 2 :=
    Finset.sum_le_sum fun i _ => sq_add_ge (x i) ((k i : ℝ))
  calc Real.exp (-α * ((x + fun i => (k i : ℝ))
        ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ))))
      ≤ Real.exp (α * μ * ∑ i, x i ^ 2
          + ∑ i, -(α * μ / 2) * (k i : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        have hsq' : (∑ i, (k i : ℝ) ^ 2) / 2 - ∑ i, x i ^ 2
            ≤ ∑ i, (x i + (k i : ℝ)) ^ 2 := by
          refine le_trans (le_of_eq ?_) hsq
          rw [Finset.sum_sub_distrib, Finset.sum_div]
        nlinarith [mul_le_mul_of_nonneg_left hQ hα.le,
          mul_le_mul_of_nonneg_left hsq' (mul_pos hα hμ).le]
    _ = Real.exp (α * μ * ∑ i, x i ^ 2)
          * ∏ i, Real.exp (-(α * μ / 2) * (k i : ℝ) ^ 2) := by
        rw [Real.exp_add, Real.exp_sum]

/-- The shifted mass is positive at every positive coupling. -/
theorem gramMass_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) : 0 < gramMass M α x := by
  have hle := (summable_gramMass hM hα x).sum_le_tsum {0}
    (fun k _ => (Real.exp_pos _).le)
  rw [Finset.sum_singleton] at hle
  exact lt_of_lt_of_le (Real.exp_pos _) hle

/-- At zero shift the mass is the Boltzmann sum of the Gram form. -/
theorem gramMass_zero (α : ℝ) : gramMass M α 0 = gramTheta M α := by
  unfold gramMass gramTheta
  refine tsum_congr fun k => ?_
  congr 1
  rw [zero_add, ← quadForm_dotProduct]

/-- The mass is invariant under integer shifts. -/
theorem gramMass_int_shift (α : ℝ) (x : Fin d → ℝ) (m : Fin d → ℤ) :
    gramMass M α (x + fun i => (m i : ℝ)) = gramMass M α x := by
  unfold gramMass
  rw [← (Equiv.addRight m).tsum_eq (fun k : Fin d → ℤ =>
    Real.exp (-α * ((x + fun i => (k i : ℝ))
      ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ)))))]
  refine tsum_congr fun k => ?_
  have hvec : ((x + fun i => (m i : ℝ)) + fun i => ((k i : ℤ) : ℝ))
      = x + fun i => (((k + m) i : ℤ) : ℝ) := by
    funext i
    show x i + (m i : ℝ) + (k i : ℝ) = x i + ((k i + m i : ℤ) : ℝ)
    push_cast
    ring
  exact congrArg
    (fun v : Fin d → ℝ => Real.exp (-α * (v ⬝ᵥ M.mulVec v))) hvec

/-! ## The decompositions -/

/-- The quadratic form scales quadratically along scalar dilation. -/
private theorem quad_smul (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (v : Fin d → ℝ) :
    (c • v) ⬝ᵥ M.mulVec (c • v) = c ^ 2 * (v ⬝ᵥ M.mulVec v) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The parallelogram law of the quadratic form — no symmetry of
`M` needed, the cross terms cancel in the sum. -/
private theorem quad_parallelogram (M : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) :
    (u + v) ⬝ᵥ M.mulVec (u + v) + (u - v) ⬝ᵥ M.mulVec (u - v)
      = 2 * (u ⬝ᵥ M.mulVec u) + 2 * (v ⬝ᵥ M.mulVec v) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add,
    dotProduct_sub, add_dotProduct, add_dotProduct, sub_dotProduct,
    sub_dotProduct]
  ring

/-- **The residue decomposition**: splitting `ℤᵈ` by residues mod
`n` writes the shifted mass as a finite sum, over residue classes,
of masses of the `n`-dilated lattice at rescaled coupling. -/
theorem gramMass_coset (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M α x
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α)
            ((n : ℝ)⁻¹ • (x + fun i => ((c i).val : ℝ))) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hsumc : Summable (fun ck : (Fin d → ZMod n) × (Fin d → ℤ) =>
      Real.exp (-α * ((x + fun i => ((piZmodProdEquiv n d ck) i : ℝ))
        ⬝ᵥ M.mulVec (x + fun i => ((piZmodProdEquiv n d ck) i : ℝ))))) :=
    (piZmodProdEquiv n d).summable_iff.mpr (summable_gramMass hM hα x)
  unfold gramMass
  rw [← (piZmodProdEquiv n d).tsum_eq (fun k : Fin d → ℤ =>
    Real.exp (-α * ((x + fun i => (k i : ℝ))
      ⬝ᵥ M.mulVec (x + fun i => (k i : ℝ))))),
    hsumc.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => tsum_congr fun k => ?_
  have hvec : ((n : ℝ)⁻¹ • (x + fun i => ((c i).val : ℝ))
        + fun i => ((k i : ℤ) : ℝ))
      = (n : ℝ)⁻¹ • (x + fun i => ((piZmodProdEquiv n d (c, k)) i : ℝ)) := by
    funext i
    show (n : ℝ)⁻¹ * (x i + ((c i).val : ℝ)) + (k i : ℝ)
        = (n : ℝ)⁻¹ * (x i + ((((c i).val : ℤ) + n * k i : ℤ) : ℝ))
    push_cast
    field_simp
    ring
  rw [hvec, quad_smul]
  congr 1
  field_simp

/-- **The parity decomposition of a product**: the product of two
shifted masses transports along `(k, m) ↦ (k+m, k−m)` — the
Gaussian splits by the parallelogram law, the image splits by
parity — into a finite sum, over parity classes, of products of
half-shifted masses at doubled coupling. -/
theorem gramMass_mul_gramMass (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      = ∑ c : Fin d → ZMod 2,
          gramMass M (2 * α)
            ((2 : ℝ)⁻¹ • (x + y + fun i => ((c i).val : ℝ)))
          * gramMass M (2 * α)
            ((2 : ℝ)⁻¹ • (x - y + fun i => ((c i).val : ℝ))) := by
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hnorm : ∀ z : Fin d → ℝ, Summable (fun k : Fin d → ℤ =>
      ‖Real.exp (-α * ((z + fun i => (k i : ℝ))
        ⬝ᵥ M.mulVec (z + fun i => (k i : ℝ))))‖) := fun z =>
    (summable_gramMass hM hα z).congr fun k =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  have hnorm2 : ∀ z : Fin d → ℝ, Summable (fun k : Fin d → ℤ =>
      ‖Real.exp (-(2 * α) * ((z + fun i => (k i : ℝ))
        ⬝ᵥ M.mulVec (z + fun i => (k i : ℝ))))‖) := fun z =>
    (summable_gramMass hM h2α z).congr fun k =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  -- the product as a sum over pairs
  unfold gramMass
  rw [tsum_mul_tsum_of_summable_norm (hnorm x) (hnorm y)]
  -- transport along the parity bijection
  have hpair : Summable
      (fun t : (Fin d → ZMod 2) × (Fin d → ℤ) × (Fin d → ℤ) =>
        Real.exp (-α * ((x + fun i =>
            (((piParityEquiv d t).1 i : ℤ) : ℝ))
          ⬝ᵥ M.mulVec (x + fun i =>
            (((piParityEquiv d t).1 i : ℤ) : ℝ))))
        * Real.exp (-α * ((y + fun i =>
            (((piParityEquiv d t).2 i : ℤ) : ℝ))
          ⬝ᵥ M.mulVec (y + fun i =>
            (((piParityEquiv d t).2 i : ℤ) : ℝ))))) :=
    (piParityEquiv d).summable_iff.mpr
      (summable_mul_of_summable_norm (hnorm x) (hnorm y))
  rw [← (piParityEquiv d).tsum_eq
      (fun km : (Fin d → ℤ) × (Fin d → ℤ) =>
        Real.exp (-α * ((x + fun i => (km.1 i : ℝ))
          ⬝ᵥ M.mulVec (x + fun i => (km.1 i : ℝ))))
        * Real.exp (-α * ((y + fun i => (km.2 i : ℝ))
          ⬝ᵥ M.mulVec (y + fun i => (km.2 i : ℝ))))),
    hpair.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  -- per parity class: rewrite each pair term by the parallelogram
  have hterm : ∀ pq : (Fin d → ℤ) × (Fin d → ℤ),
      Real.exp (-α * ((x + fun i =>
          (((piParityEquiv d (c, pq)).1 i : ℤ) : ℝ))
        ⬝ᵥ M.mulVec (x + fun i =>
          (((piParityEquiv d (c, pq)).1 i : ℤ) : ℝ))))
      * Real.exp (-α * ((y + fun i =>
          (((piParityEquiv d (c, pq)).2 i : ℤ) : ℝ))
        ⬝ᵥ M.mulVec (y + fun i =>
          (((piParityEquiv d (c, pq)).2 i : ℤ) : ℝ))))
      = Real.exp (-(2 * α)
          * ((((2 : ℝ)⁻¹ • (x + y + fun i => ((c i).val : ℝ)))
              + fun i => (pq.1 i : ℝ))
            ⬝ᵥ M.mulVec ((((2 : ℝ)⁻¹
              • (x + y + fun i => ((c i).val : ℝ))))
              + fun i => (pq.1 i : ℝ))))
        * Real.exp (-(2 * α)
          * ((((2 : ℝ)⁻¹ • (x - y + fun i => ((c i).val : ℝ)))
              + fun i => (pq.2 i : ℝ))
            ⬝ᵥ M.mulVec ((((2 : ℝ)⁻¹
              • (x - y + fun i => ((c i).val : ℝ))))
              + fun i => (pq.2 i : ℝ)))) := by
    rintro ⟨p, q⟩
    set U : Fin d → ℝ := x + fun i =>
      (((piParityEquiv d (c, p, q)).1 i : ℤ) : ℝ) with hU
    set V : Fin d → ℝ := y + fun i =>
      (((piParityEquiv d (c, p, q)).2 i : ℤ) : ℝ) with hV
    have hA : ((2 : ℝ)⁻¹ • (x + y + fun i => ((c i).val : ℝ))
          + fun i => (p i : ℝ)) = (2 : ℝ)⁻¹ • (U + V) := by
      funext i
      show (2 : ℝ)⁻¹ * (x i + y i + ((c i).val : ℝ)) + (p i : ℝ)
          = (2 : ℝ)⁻¹ * ((x i + (((c i).val : ℤ) + p i + q i : ℤ))
            + (y i + ((p i - q i : ℤ) : ℝ)))
      push_cast
      ring
    have hB : ((2 : ℝ)⁻¹ • (x - y + fun i => ((c i).val : ℝ))
          + fun i => (q i : ℝ)) = (2 : ℝ)⁻¹ • (U - V) := by
      funext i
      show (2 : ℝ)⁻¹ * (x i - y i + ((c i).val : ℝ)) + (q i : ℝ)
          = (2 : ℝ)⁻¹ * ((x i + (((c i).val : ℤ) + p i + q i : ℤ))
            - (y i + ((p i - q i : ℤ) : ℝ)))
      push_cast
      ring
    rw [← Real.exp_add, ← Real.exp_add, hA, hB, quad_smul, quad_smul]
    congr 1
    have hpar := quad_parallelogram M U V
    linear_combination (α / 2) * hpar
  rw [tsum_congr hterm]
  -- contract the pair sum into a product of masses
  rw [← tsum_mul_tsum_of_summable_norm
    (hnorm2 ((2 : ℝ)⁻¹ • (x + y + fun i => ((c i).val : ℝ))))
    (hnorm2 ((2 : ℝ)⁻¹ • (x - y + fun i => ((c i).val : ℝ))))]

/-- The mass is even in the shift. -/
theorem gramMass_neg (α : ℝ) (x : Fin d → ℝ) :
    gramMass M α (-x) = gramMass M α x := by
  unfold gramMass
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  refine tsum_congr fun k => ?_
  congr 1
  show -α * ((-x + fun i => (((-k) i : ℤ) : ℝ))
      ⬝ᵥ M.mulVec (-x + fun i => (((-k) i : ℤ) : ℝ))) = _
  have h : (-x + fun i => (((-k) i : ℤ) : ℝ))
      = -(x + fun i => ((k i : ℤ) : ℝ)) := by
    funext i
    show -x i + ((-k i : ℤ) : ℝ) = -(x i + (k i : ℝ))
    push_cast
    ring
  rw [h, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

end Theaetetus
