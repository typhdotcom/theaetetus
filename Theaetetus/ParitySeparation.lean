import Theaetetus.MassMaximum

/-! # Separation of the parity feature vectors

The `2^d` entries of `parityVector M α z` are the half-shifted
masses of the parity cosets. For `M` positive definite and `α > 0`,
up to one factor common to every entry, they are the second-order
theta coordinates of a purely imaginary period matrix proportional
to `M` — positive definiteness and a positive coupling are what make
that matrix a Siegel point at all. For an *indecomposable*
principally polarized abelian variety the map those coordinates
define is the Kummer embedding: it is two-to-one, identifying `z`
with `−z` and nothing else. A decomposable variety instead carries
one sign per factor, so no single global sign describes its fibers.

Separation is therefore not a theorem available here — Siegel theta
is not constructed in this development, and the classical statement
is conditional on indecomposability. It is taken as a named
hypothesis in the normalization used here (`ParitySeparating`),
motivated by that map, and this module settles what it is worth and
where it is unavailable.

What it is worth is the whole coprime rigidity statement. The
criterion `TwoGridReflection M s a b` asserts

    parityVector (v_r + v_c) = parityVector (v_r − v_c)

for *every* pair of residues. Separation turns each such equality
into `v_c ∈ ℤᵈ` or `v_r ∈ ℤᵈ`, and a residue shift is a lattice
shift only at the zero class (`isLatticeShift_residueShift_iff`). At
`a, b > 1` in positive rank both classes can be chosen nonzero at
once, so the criterion fails and the coprime defect is strictly
negative (`not_twoGridReflection_of_paritySeparating`,
`gramDefect_neg_of_paritySeparating`).

Where it is unavailable is proved in one direction only. If the
coordinates split into two blocks with no cross terms, negating one
block preserves both the form and the lattice, so it preserves every
entry of the parity vector (`gramMass_flipCoords`,
`parityVector_flipCoords`) while moving the point off `±z`. Hence
every proper coordinate block splitting destroys separation
(`not_paritySeparating_of_split`): such a form carries one sign per
block, not one sign overall. The converse — that separation holds
whenever no such splitting exists — is not proved here, and neither
is the reduction of a split form to its blocks through the
orthogonal-sum defect theorem. -/

namespace Theaetetus

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- **Separation up to sign**, as a hypothesis: two shifts with the
same parity feature vector agree modulo `2ℤᵈ` up to sign. For `M`
positive definite and `α > 0` this is the normalized form of the
classical statement about second-order theta coordinates on an
indecomposable principally polarized abelian variety, read on the
real locus; the predicate is stated for arbitrary parameters, and it
is assumed, never proved, in this development. -/
def ParitySeparating (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : Prop :=
  ∀ z w : Fin d → ℝ, parityVector M α z = parityVector M α w →
    IsLatticeShift ((2 : ℝ)⁻¹ • (z - w))
      ∨ IsLatticeShift ((2 : ℝ)⁻¹ • (z + w))

/-! ## What separation would settle -/

private theorem half_sub_residue {a b : ℕ} (r : Fin d → ZMod b)
    (c : Fin d → ZMod a) :
    (2 : ℝ)⁻¹ • ((residueShift b r + residueShift a c)
      - (residueShift b r - residueShift a c)) = residueShift a c := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem half_add_residue {a b : ℕ} (r : Fin d → ZMod b)
    (c : Fin d → ZMod a) :
    (2 : ℝ)⁻¹ • ((residueShift b r + residueShift a c)
      + (residueShift b r - residueShift a c)) = residueShift b r := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The rigidity statement, conditional on separation**: in
positive rank, at dilations above one, a separating form admits no
two-grid reflection. Each reflected equality would force either the
displacement class or the anchor class to be trivial, and both can be
chosen nontrivial at once. -/
theorem not_twoGridReflection_of_paritySeparating (hd : 0 < d) {s : ℝ}
    {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hsep : ParitySeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    ¬ TwoGridReflection M s a b := by
  have : Fact (1 < a) := ⟨ha⟩
  have : Fact (1 < b) := ⟨hb⟩
  intro h
  have hi : Fin d := ⟨0, hd⟩
  have hcases := hsep _ _ (h (fun _ => 1) (fun _ => 1))
  rw [half_sub_residue, half_add_residue] at hcases
  rcases hcases with hc | hr
  · have := (isLatticeShift_residueShift_iff (by omega : 0 < a) _).mp hc
    exact one_ne_zero (congrFun this hi)
  · have := (isLatticeShift_residueShift_iff (by omega : 0 < b) _).mp hr
    exact one_ne_zero (congrFun this hi)

/-- The same statement read on the defect: a separating
positive-definite form has strictly nonzero — hence, with the sign
theorem, strictly negative — defect at every coprime pair above
one. -/
theorem gramDefect_ne_zero_of_paritySeparating (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (hsep : ParitySeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b ≠ 0 := fun hzero =>
  not_twoGridReflection_of_paritySeparating hd ha hb hsep
    ((gramDefect_eq_zero_iff_twoGridReflection hM hs (by omega) (by omega)
      hco).mp hzero)

/-- The sign form: with the correlation bound, a separating
positive-definite form has strictly negative defect at every coprime
pair above one — the full coprime rigidity statement for such a
form. -/
theorem gramDefect_neg_of_paritySeparating (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (hsep : ParitySeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 :=
  lt_of_le_of_ne (gramDefect_nonpos hM hs (by omega) (by omega))
    (gramDefect_ne_zero_of_paritySeparating hM hd hs ha hb hco hsep)

/-! ## Where separation fails: the decomposable forms -/

/-- Negation on a block of coordinates. -/
def flipCoords {R : Type*} [Neg R] (T : Finset (Fin d)) (x : Fin d → R) :
    Fin d → R := fun i => if i ∈ T then -x i else x i

theorem flipCoords_flipCoords {R : Type*} [SubtractionMonoid R]
    (T : Finset (Fin d)) (x : Fin d → R) :
    flipCoords T (flipCoords T x) = x := by
  funext i
  by_cases hi : i ∈ T <;> simp [flipCoords, hi]

/-- The block negation as a permutation of the lattice. -/
def flipEquiv (T : Finset (Fin d)) : (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun := flipCoords T
  invFun := flipCoords T
  left_inv := flipCoords_flipCoords T
  right_inv := flipCoords_flipCoords T

theorem flipCoords_intCast (T : Finset (Fin d)) (k : Fin d → ℤ) :
    (fun i => (((flipCoords T k) i : ℤ) : ℝ))
      = flipCoords T (fun i => ((k i : ℤ) : ℝ)) := by
  funext i
  by_cases hi : i ∈ T <;> simp [flipCoords, hi]

/-- A block negation preserves the quadratic form exactly when the
block carries no cross terms. -/
theorem quadForm_flipCoords {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) (x : Fin d → ℝ) :
    flipCoords T x ⬝ᵥ M.mulVec (flipCoords T x) = x ⬝ᵥ M.mulVec x := by
  rw [← quadForm_dotProduct, ← quadForm_dotProduct]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
    simp only [flipCoords, hi, hj, ite_true, ite_false]
  · ring
  · rw [hT i j (by simp [hi, hj])]; ring
  · rw [hT i j (by simp [hi, hj])]; ring

/-- **Block negation is a mass symmetry**: on a form with no cross
terms across the block, negating that block preserves both the
quadratic form and the lattice, so it preserves every shifted
mass. -/
theorem gramMass_flipCoords {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) (α : ℝ) (x : Fin d → ℝ) :
    gramMass M α (flipCoords T x) = gramMass M α x := by
  have hterm : ∀ k : Fin d → ℤ,
      Real.exp (-α * ((flipCoords T x + fun i => ((k i : ℤ) : ℝ))
          ⬝ᵥ M.mulVec (flipCoords T x + fun i => ((k i : ℤ) : ℝ))))
        = Real.exp (-α * ((x + fun i => (((flipEquiv T k) i : ℤ) : ℝ))
          ⬝ᵥ M.mulVec (x + fun i => (((flipEquiv T k) i : ℤ) : ℝ)))) := by
    intro k
    refine congrArg Real.exp (congrArg (fun t => -α * t) ?_)
    rw [← quadForm_flipCoords hT
      (x + fun i => (((flipEquiv T k) i : ℤ) : ℝ))]
    refine congrArg (fun y => y ⬝ᵥ M.mulVec y) ?_
    show _ = flipCoords T (x + fun i => (((flipCoords T k) i : ℤ) : ℝ))
    rw [flipCoords_intCast]
    funext i
    by_cases hi : i ∈ T <;>
      simp [flipCoords, hi, add_comm]
  exact (tsum_congr hterm).trans ((flipEquiv T).tsum_eq
    (fun k : Fin d → ℤ => Real.exp (-α * ((x + fun i => ((k i : ℤ) : ℝ))
      ⬝ᵥ M.mulVec (x + fun i => ((k i : ℤ) : ℝ))))))

/-- The parity feature vector inherits the block symmetry entrywise:
the parity digit only moves the shift by an integer vector. -/
theorem parityVector_flipCoords {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) (α : ℝ) (z : Fin d → ℝ)
    (c : Fin d → ZMod 2) :
    parityVector M α (flipCoords T z) c = parityVector M α z c := by
  set u : Fin d → ℝ := (2 : ℝ)⁻¹ • (z + fun i => (((c i).val : ℕ) : ℝ))
    with hu
  set m : Fin d → ℤ := fun i => if i ∈ T then (((c i).val : ℕ) : ℤ) else 0
    with hm
  have hshift : (2 : ℝ)⁻¹ • (flipCoords T z
      + fun i => (((c i).val : ℕ) : ℝ))
      = flipCoords T u + fun i => ((m i : ℤ) : ℝ) := by
    funext i
    by_cases hi : i ∈ T <;>
      simp only [hu, hm, flipCoords, hi, ite_true, ite_false, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul, Int.cast_natCast, Int.cast_zero] <;>
      ring
  show gramMass M (2 * α) _ = gramMass M (2 * α) _
  rw [hshift, gramMass_int_shift, gramMass_flipCoords hT]

/-- **Every proper block splitting destroys separation**: a form
whose coordinates split with no cross terms carries one sign per
block, not one sign overall. The witness is a shift with the same
nonintegral coordinate everywhere; negating one block fixes the
whole parity vector while leaving both `z − w` and `z + w` off the
doubled lattice. Only this direction is proved: nothing here says
separation holds when no such splitting exists. -/
theorem not_paritySeparating_of_split {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) (α : ℝ) : ¬ ParitySeparating M α := by
  have hthird : ∀ k : ℤ, ((3 : ℝ)⁻¹ : ℝ) ≠ (k : ℝ) := by
    intro k hk
    have h3 : (3 : ℝ) * (3 : ℝ)⁻¹ = 1 := by norm_num
    rw [hk] at h3
    have : (3 : ℤ) * k = 1 := by exact_mod_cast h3
    omega
  intro hsep
  set z : Fin d → ℝ := fun _ => (3 : ℝ)⁻¹ with hz
  have heq : parityVector M α z = parityVector M α (flipCoords T z) := by
    funext c
    exact (parityVector_flipCoords hT α z c).symm
  rcases hsep _ _ heq with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine hthird (k i₀) ?_
    have h := congrFun hk i₀
    simp only [hz, flipCoords, hi₀, ite_true, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, sub_neg_eq_add] at h
    linarith
  · refine hthird (k j₀) ?_
    have h := congrFun hk j₀
    simp only [hz, flipCoords, hj₀, ite_false, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul] at h
    linarith

end Theaetetus
