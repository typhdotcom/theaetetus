import Theaetetus.ParitySeparation

/-! # The real Gaussian core of separation

`ParitySeparating` was named after the classical statement about
second-order theta coordinates. That statement is classically proved
through the zero divisor of the theta function, and the shifted mass
has no zeros, so the argument does not descend directly to one
phrased in the positive real mass alone. It could still be imported
through complex geometry; this module opens a purely real
alternative, and completing it requires the Fourier certificate
described below. What the real locus consumes is a statement about
the logarithmic mass — no theta function, no abelian variety, no
symplectic geometry.

The reduction is one application of the addition identity
`gramMass_mul_eq_inner`, which is the theta addition formula in this
normalization. Pairing both sides of an equality of parity vectors
against the vector at an arbitrary displacement turns a `2^d`-entry
equality into a one-parameter family of scalar identities

    m((z+u)/2)·m((z−u)/2) = m((w+u)/2)·m((w−u)/2)

(`gramMass_reflect_prod_of_parityVector_eq`), and taking logarithms
— legitimate, the masses being strictly positive — says that the
even part of the logarithmic mass about `z/2` equals the even part
about `w/2` (`logMass_even_part_eq_of_parityVector_eq`).

So separation follows from the property that the even part of the
logarithmic mass about a point determines that point up to sign
(`EvenPartSeparating`, `paritySeparating_of_evenPartSeparating`),
and with it the whole coprime rigidity statement
(`gramDefect_neg_of_evenPartSeparating`). A form whose coordinates
split with no cross terms fails the even-part property too
(`not_evenPartSeparating_of_split`); that proof is contraposition
through `not_paritySeparating_of_split`, not a computation with
frequencies.

The arithmetic that the analytic layer will consume is separated out
here (`isLatticeShift_or_of_pairwise`): given that every coordinate
lies on the integral difference branch or the integral sum branch,
and every distinct pair has its coordinate sum on one of the two,
one branch serves the whole vector. A coordinate satisfying both
branches is flexible and adopts whichever branch survives; the pair
hypothesis rules out only the coexistence of a coordinate forced
onto one branch with a coordinate forced onto the other. -/

namespace Theaetetus

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- The logarithmic shifted mass. -/
noncomputable def logMass (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (x : Fin d → ℝ) : ℝ := Real.log (gramMass M α x)

/-! ## From a vector equality to a scalar family -/

private theorem half_add_half_sub (z u : Fin d → ℝ) :
    (2 : ℝ)⁻¹ • (z + u) + (2 : ℝ)⁻¹ • (z - u) = z := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem half_sub_half_sub (z u : Fin d → ℝ) :
    (2 : ℝ)⁻¹ • (z + u) - (2 : ℝ)⁻¹ • (z - u) = u := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The reduction to a scalar family**: equal parity vectors make
the reflected mass products agree at every displacement. Pairing the
addition identity against the parity vector at `u` replaces a
`2^d`-entry equality by a one-parameter family of scalar Gaussian
identities. -/
theorem gramMass_reflect_prod_of_parityVector_eq (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {z w : Fin d → ℝ}
    (h : parityVector M α z = parityVector M α w) (u : Fin d → ℝ) :
    gramMass M α ((2 : ℝ)⁻¹ • (z + u))
        * gramMass M α ((2 : ℝ)⁻¹ • (z - u))
      = gramMass M α ((2 : ℝ)⁻¹ • (w + u))
        * gramMass M α ((2 : ℝ)⁻¹ • (w - u)) := by
  rw [gramMass_mul_eq_inner hM hα ((2 : ℝ)⁻¹ • (z + u))
      ((2 : ℝ)⁻¹ • (z - u)),
    gramMass_mul_eq_inner hM hα ((2 : ℝ)⁻¹ • (w + u))
      ((2 : ℝ)⁻¹ • (w - u)),
    half_add_half_sub, half_sub_half_sub, half_add_half_sub,
    half_sub_half_sub, h]

/-- The same statement logarithmically: the even part of the
logarithmic mass about `z/2` agrees with the even part about `w/2`. -/
theorem logMass_even_part_eq_of_parityVector_eq (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {z w : Fin d → ℝ}
    (h : parityVector M α z = parityVector M α w) (v : Fin d → ℝ) :
    logMass M α ((2 : ℝ)⁻¹ • z + v) + logMass M α ((2 : ℝ)⁻¹ • z - v)
      = logMass M α ((2 : ℝ)⁻¹ • w + v)
        + logMass M α ((2 : ℝ)⁻¹ • w - v) := by
  have hsplit : ∀ t : Fin d → ℝ,
      (2 : ℝ)⁻¹ • (t + (2 : ℝ) • v) = (2 : ℝ)⁻¹ • t + v
        ∧ (2 : ℝ)⁻¹ • (t - (2 : ℝ) • v) = (2 : ℝ)⁻¹ • t - v := by
    intro t
    constructor <;> funext i <;>
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] <;>
      ring
  have hz := hsplit z
  have hw := hsplit w
  have hprod := gramMass_reflect_prod_of_parityVector_eq hM hα h
    ((2 : ℝ) • v)
  rw [hz.1, hz.2, hw.1, hw.2] at hprod
  simp only [logMass]
  rw [← Real.log_mul (gramMass_pos hM hα _).ne' (gramMass_pos hM hα _).ne',
    ← Real.log_mul (gramMass_pos hM hα _).ne' (gramMass_pos hM hα _).ne',
    hprod]

/-! ## The finite sign-globalization lemma -/

/-- **Sign globalization**, a statement of pure arithmetic. Suppose
every coordinate lies on the integral difference branch or the
integral sum branch, and every distinct pair has its coordinate sum
on one of those two branches. Then one branch serves the whole
vector.

The pair hypothesis does not force a branch on any single
coordinate. A coordinate may satisfy both branches — `p i` and `q i`
both integral — and such a coordinate is flexible: it adopts
whichever branch the rest of the vector settles on. What the pair
hypothesis rules out is the coexistence of a coordinate forced onto
the difference branch with one forced onto the sum branch, since for
such a pair both coordinate sums are nonintegral. -/
theorem isLatticeShift_or_of_pairwise {p q : Fin d → ℝ}
    (h1 : ∀ i, (∃ k : ℤ, p i = (k : ℝ)) ∨ (∃ k : ℤ, q i = (k : ℝ)))
    (h2 : ∀ i j, i ≠ j → (∃ k : ℤ, p i + p j = (k : ℝ))
      ∨ (∃ k : ℤ, q i + q j = (k : ℝ))) :
    IsLatticeShift p ∨ IsLatticeShift q := by
  by_cases hforced : ∃ j, (∃ k : ℤ, q j = (k : ℝ))
      ∧ ¬ (∃ k : ℤ, p j = (k : ℝ))
  · right
    rw [isLatticeShift_iff_forall]
    intro i
    obtain ⟨j, hqj, hpj⟩ := hforced
    by_cases hi : ∃ k : ℤ, q i = (k : ℝ)
    · exact hi
    · exfalso
      have hdi : ∃ k : ℤ, p i = (k : ℝ) := (h1 i).resolve_right hi
      have hij : i ≠ j := by
        rintro rfl
        exact hpj hdi
      rcases h2 i j hij with hp | hq
      · obtain ⟨k, hk⟩ := hp
        obtain ⟨k', hk'⟩ := hdi
        exact hpj ⟨k - k', by push_cast; linarith⟩
      · obtain ⟨k, hk⟩ := hq
        obtain ⟨k', hk'⟩ := hqj
        exact hi ⟨k - k', by push_cast; linarith⟩
  · left
    rw [isLatticeShift_iff_forall]
    intro i
    push Not at hforced
    exact (h1 i).elim id fun hs => hforced i hs

/-! ## The analytic property that remains -/

/-- **Even-part separation**: the even part of the logarithmic mass
about a point determines that point up to sign, modulo the lattice.
This is the real-locus statement that coprime rigidity consumes; it
is assumed, never proved, in this development. -/
def EvenPartSeparating (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) : Prop :=
  ∀ a b : Fin d → ℝ,
    (∀ v : Fin d → ℝ, logMass M α (a + v) + logMass M α (a - v)
        = logMass M α (b + v) + logMass M α (b - v)) →
      IsLatticeShift (a - b) ∨ IsLatticeShift (a + b)

/-- **The core implication**: even-part separation gives separation
of the parity feature vectors. -/
theorem paritySeparating_of_evenPartSeparating (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (h : EvenPartSeparating M α) : ParitySeparating M α := by
  intro z w hzw
  have hsub : (2 : ℝ)⁻¹ • z - (2 : ℝ)⁻¹ • w = (2 : ℝ)⁻¹ • (z - w) :=
    (smul_sub _ _ _).symm
  have hadd : (2 : ℝ)⁻¹ • z + (2 : ℝ)⁻¹ • w = (2 : ℝ)⁻¹ • (z + w) :=
    (smul_add _ _ _).symm
  have hcases := h _ _
    (logMass_even_part_eq_of_parityVector_eq hM hα hzw)
  rwa [hsub, hadd] at hcases

/-- Coprime rigidity from the real-locus property alone. -/
theorem not_twoGridReflection_of_evenPartSeparating (hM : M.PosDef)
    (hd : 0 < d) {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (h : EvenPartSeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    ¬ TwoGridReflection M s a b := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hβ : (0 : ℝ) < (a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s) := by positivity
  exact not_twoGridReflection_of_paritySeparating hd ha hb
    (paritySeparating_of_evenPartSeparating hM hβ h)

theorem gramDefect_neg_of_evenPartSeparating (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (h : EvenPartSeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hbR : (0 : ℝ) < (b : ℝ) := by positivity
  have hβ : (0 : ℝ) < (a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s) := by positivity
  exact gramDefect_neg_of_paritySeparating hM hd hs ha hb hco
    (paritySeparating_of_evenPartSeparating hM hβ h)

/-- The block obstruction transports: a form whose coordinates split
with no cross terms fails even-part separation too. -/
theorem not_evenPartSeparating_of_split (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) : ¬ EvenPartSeparating M α := fun h =>
  not_paritySeparating_of_split hT hi₀ hj₀ α
    (paritySeparating_of_evenPartSeparating hM hα h)

end Theaetetus
