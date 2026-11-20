import Theaetetus.SiegelTuples

/-! # Even quadruples are degree-four Siegel data

The **even quadruples** at energy `m` are the quadruples of sectors of
energy `m` whose sum lies in `2ℤⁿ`. Over the classes of `ℤⁿ ⧸ 2ℤⁿ`
they count `∑_c (∑_{Q(x)=m} (−1)^⟨x,c⟩)⁴ / 2ⁿ`, the fourth moment of
the twisted shells, and at `m = 2` on an even unimodular lattice they
are the root quadruples whose count `N₄` is the coefficient of the
classwise degree-four law.

For a symmetric Gram matrix, an even quadruple `(u₀, u₁, u₂, u₃)` is
the same thing as `(u₀, u₁, u₂, w)` with `u₃ = 2w − u₀ − u₁ − u₂`,
and every condition is a condition on the Gram matrix of
`(u₀, u₁, u₂, w)` (`evenQuadsEquivPred`). Sorting by Gram matrix
(`gramFiberEquiv`), equal degree-four representation numbers give
equivalent even quadruples (`evenQuadsEquivOfSiegel`); no positivity
is needed. -/

namespace Theaetetus

open Matrix

variable {n : ℕ}

/-- Quadruples of sectors of energy `m` whose sum lies in `2ℤⁿ`. -/
def evenQuads (G : Matrix (Fin n) (Fin n) ℤ) (m : ℤ) : Set (Fin 4 → Fin n → ℤ) :=
  {U | (∀ i, intEnergy G (U i) = m) ∧ ∀ l, (2 : ℤ) ∣ U 0 l + U 1 l + U 2 l + U 3 l}

theorem gramPairing_add_left (G : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    gramPairing G (x + y) z = gramPairing G x z + gramPairing G y z := by
  simp [gramPairing, add_dotProduct]

theorem gramPairing_add_right (G : Matrix (Fin n) (Fin n) ℤ) (x y z : Fin n → ℤ) :
    gramPairing G x (y + z) = gramPairing G x y + gramPairing G x z := by
  simp [gramPairing, mulVec_add, dotProduct_add]

/-- The energy of the fourth sector in Gram coordinates. -/
theorem intEnergy_fourth {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm)
    (a b c w : Fin n → ℤ) :
    intEnergy G ((2 : ℤ) • w - (a + b + c))
      = 4 * intEnergy G w + (intEnergy G a + intEnergy G b + intEnergy G c
          + 2 * (gramPairing G a b + gramPairing G a c + gramPairing G b c))
        - 4 * (gramPairing G w a + gramPairing G w b + gramPairing G w c) := by
  rw [intEnergy_sub hG, intEnergy_two_smul, intEnergy_add hG, intEnergy_add hG]
  simp only [gramPairing_add_left, gramPairing_add_right]
  simp only [gramPairing, smul_dotProduct, smul_eq_mul]
  ring

/-- The Gram conditions of an even quadruple, in the coordinates
`(u₀, u₁, u₂, w)`. -/
def evenQuadPred (m : ℤ) (T : Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  T 0 0 = m ∧ T 1 1 = m ∧ T 2 2 = m ∧
    4 * T 3 3 + (T 0 0 + T 1 1 + T 2 2 + 2 * (T 0 1 + T 0 2 + T 1 2))
      - 4 * (T 3 0 + T 3 1 + T 3 2) = m

/-- The half sum of an even quadruple. -/
def halfSum (U : Fin 4 → Fin n → ℤ) : Fin n → ℤ :=
  fun l => (U 0 l + U 1 l + U 2 l + U 3 l) / 2

/-- **Even quadruples are Gram data.** -/
def evenQuadsEquivPred {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm) (m : ℤ) :
    evenQuads G m ≃ {Y : Fin 4 → Fin n → ℤ // evenQuadPred m (tupleGram G Y)} where
  toFun U := ⟨![U.1 0, U.1 1, U.1 2, halfSum U.1], by
    obtain ⟨U, hE, hd⟩ := U
    have h3 : U 3 = (2 : ℤ) • halfSum U - (U 0 + U 1 + U 2) := by
      funext l
      simp only [halfSum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Int.mul_ediv_cancel' (hd l)]
      ring
    have h := hE 3
    rw [h3, intEnergy_fourth hG] at h
    refine ⟨hE 0, hE 1, hE 2, ?_⟩
    simpa [tupleGram, intEnergy_eq_gramPairing] using h⟩
  invFun Y := ⟨![Y.1 0, Y.1 1, Y.1 2, (2 : ℤ) • Y.1 3 - (Y.1 0 + Y.1 1 + Y.1 2)], by
    obtain ⟨Y, h0, h1, h2, h3⟩ := Y
    refine ⟨fun i => ?_, fun l => ?_⟩
    · fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · show intEnergy G ((2 : ℤ) • Y 3 - (Y 0 + Y 1 + Y 2)) = m
        rw [intEnergy_fourth hG]
        simpa [tupleGram, intEnergy_eq_gramPairing] using h3
    · exact ⟨Y 3 l, by simp⟩⟩
  left_inv U := by
    obtain ⟨U, hE, hd⟩ := U
    apply Subtype.ext
    funext i l
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show 2 * halfSum U l - (U 0 l + U 1 l + U 2 l) = U 3 l
      simp only [halfSum]
      rw [Int.mul_ediv_cancel' (hd l)]
      ring
  right_inv Y := by
    obtain ⟨Y, hY⟩ := Y
    apply Subtype.ext
    funext i l
    fin_cases i
    · rfl
    · rfl
    · rfl
    · simp [halfSum]

/-- **Equal degree-four representation numbers give equivalent even
quadruples.** -/
noncomputable def evenQuadsEquivOfSiegel {G G' : Matrix (Fin n) (Fin n) ℤ}
    (hG : G.IsSymm) (hG' : G'.IsSymm)
    (h : ∀ T : Matrix (Fin 4) (Fin 4) ℤ, Nonempty (siegelSetK G T ≃ siegelSetK G' T))
    (m : ℤ) : evenQuads G m ≃ evenQuads G' m :=
  (evenQuadsEquivPred hG m).trans <| (gramFiberEquiv G (evenQuadPred m)).trans <|
    (Equiv.sigmaCongrRight (β₁ := fun T : {T // evenQuadPred m T} => siegelSetK G T.1)
      fun T => (h T.1).some).trans <|
      (gramFiberEquiv G' (evenQuadPred m)).symm.trans (evenQuadsEquivPred hG' m).symm

end Theaetetus
