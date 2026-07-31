import Theaetetus.Correlation

/-! # The orthogonal sum: partition functions multiply, defects add

The orthogonal sum of two lattice actions
(`QuadLatticeAction.orthSum`): the product lattice with the sum
form and no cross terms. Its partition function is the product of
the factors' (`QuadLatticeAction.orthSum_scaledPartFn`), so by the
additivity of description costs the intrinsic defect is the sum of
the factors' defects (`QuadLatticeAction.orthSum_defect`). Since
every factor's defect is nonpositive, vanishing is equivalent to
vanishing of every factor
(`QuadLatticeAction.orthSum_defect_eq_zero_iff`) — a zero-defect
pair of resolutions on an orthogonal sum is a zero-defect pair on
each factor. At real scale the strict rectangle inequality is
preserved by orthogonal sums
(`QuadLatticeAction.orthSum_rect_strict`), so any failure of
strictness descends to a factor
(`QuadLatticeAction.rect_strict_descend`) — a strictness
counterexample descends through every orthogonal
decomposition. -/

namespace Theaetetus

open Matrix

universe u

namespace QuadLatticeAction

variable (Q Q' : QuadLatticeAction.{u})

/-- **The orthogonal sum of two lattice actions**: the product
lattice carrying the sum form — no cross terms. Positive
definiteness is discharged at the product chart, whose Gram is
block diagonal. -/
noncomputable def orthSum : QuadLatticeAction.{u} :=
  letI : Module ℤ (Q.Λ × Q'.Λ) := Prod.instModule
  letI : Module.Free ℤ (Q.Λ × Q'.Λ) :=
    Module.Free.of_basis
      ((Module.finBasis ℤ Q.Λ).prod (Module.finBasis ℤ Q'.Λ))
  letI : Module.Finite ℤ (Q.Λ × Q'.Λ) :=
    Module.Finite.of_basis
      ((Module.finBasis ℤ Q.Λ).prod (Module.finBasis ℤ Q'.Λ))
  { Λ := Q.Λ × Q'.Λ
    form := fun p p' => Q.form p.1 p'.1 + Q'.form p.2 p'.2
    form_comm := fun p p' => by rw [Q.form_comm, Q'.form_comm]
    form_add_left := fun p₁ p₂ p' => by
      show Q.form (p₁.1 + p₂.1) p'.1 + Q'.form (p₁.2 + p₂.2) p'.2 = _
      rw [Q.form_add_left, Q'.form_add_left]
      ring
    posDef_baseChange := by
      set b := Module.finBasis ℤ Q.Λ with hb
      set b' := Module.finBasis ℤ Q'.Λ with hb'
      refine bilinBaseChange_posDef_of_gram _ _ _
        ((b.prod b').reindex finSumFinEquiv) ?_
      set bb := (b.prod b').reindex finSumFinEquiv with hbb
      have hLfst : ∀ k, (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).1
          = b k := by
        intro k
        rw [hbb, Module.Basis.reindex_apply,
          finSumFinEquiv_symm_apply_castAdd]
        exact Module.Basis.prod_apply_inl_fst b b' k
      have hLsnd : ∀ k, (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).2
          = 0 := by
        intro k
        rw [hbb, Module.Basis.reindex_apply,
          finSumFinEquiv_symm_apply_castAdd]
        exact Module.Basis.prod_apply_inl_snd b b' k
      have hRfst : ∀ k, (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).1
          = 0 := by
        intro k
        rw [hbb, Module.Basis.reindex_apply,
          finSumFinEquiv_symm_apply_natAdd]
        exact Module.Basis.prod_apply_inr_fst b b' k
      have hRsnd : ∀ k, (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).2
          = b' k := by
        intro k
        rw [hbb, Module.Basis.reindex_apply,
          finSumFinEquiv_symm_apply_natAdd]
        exact Module.Basis.prod_apply_inr_snd b b' k
      have hzr : ∀ a : Q.Λ, Q.form a 0 = 0 := fun a => by
        rw [Q.form_comm, Q.form_zero_left]
      have hzr' : ∀ a : Q'.Λ, Q'.form a 0 = 0 := fun a => by
        rw [Q'.form_comm, Q'.form_zero_left]
      refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun c hc => ?_⟩
      · ext i j
        show star (Q.form (bb j).1 (bb i).1 + Q'.form (bb j).2 (bb i).2)
            = Q.form (bb i).1 (bb j).1 + Q'.form (bb i).2 (bb j).2
        rw [star_trivial, Q.form_comm, Q'.form_comm]
      · have hstar : star c = c := funext fun i => star_trivial _
        rw [hstar]
        -- the quadratic form splits into the two block forms
        have hexpand : c ⬝ᵥ (Matrix.of fun i j =>
              Q.form (bb i).1 (bb j).1
                + Q'.form (bb i).2 (bb j).2).mulVec c
            = (∑ i, ∑ j, Q.form (bb i).1 (bb j).1 * c i * c j)
              + ∑ i, ∑ j, Q'.form (bb i).2 (bb j).2 * c i * c j := by
          rw [← quadForm_dotProduct, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.of_apply]
          ring
        have hA : (∑ i, ∑ j, Q.form (bb i).1 (bb j).1 * c i * c j)
            = (fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)) ⬝ᵥ
                (Q.gram b).mulVec
                  (fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)) := by
          rw [Fin.sum_univ_add (f := fun i =>
            ∑ j, Q.form (bb i).1 (bb j).1 * c i * c j)]
          rw [show (∑ k, ∑ j,
                Q.form (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).1
                  (bb j).1
                * c (Fin.natAdd (Module.finrank ℤ Q.Λ) k) * c j) = 0 from
            Finset.sum_eq_zero fun k _ =>
              Finset.sum_eq_zero fun j _ => by
                rw [hRfst, Q.form_zero_left]
                ring]
          rw [add_zero]
          calc ∑ k, ∑ j,
              Q.form (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).1
                (bb j).1
              * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k) * c j
              = ∑ k, ∑ l, Q.gram b k l
                  * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)
                  * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) l) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Fin.sum_univ_add (f := fun j =>
                  Q.form (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).1
                    (bb j).1
                  * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k) * c j)]
                rw [show (∑ l,
                      Q.form (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).1
                        (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) l)).1
                      * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)
                      * c (Fin.natAdd (Module.finrank ℤ Q.Λ) l)) = 0 from
                  Finset.sum_eq_zero fun l _ => by
                    rw [hRfst, hzr]
                    ring]
                rw [add_zero]
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [hLfst, hLfst, gram_apply]
            _ = _ := quadForm_dotProduct (Q.gram b) _
        have hB : (∑ i, ∑ j, Q'.form (bb i).2 (bb j).2 * c i * c j)
            = (fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)) ⬝ᵥ
                (Q'.gram b').mulVec
                  (fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)) := by
          rw [Fin.sum_univ_add (f := fun i =>
            ∑ j, Q'.form (bb i).2 (bb j).2 * c i * c j)]
          rw [show (∑ k, ∑ j,
                Q'.form (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)).2
                  (bb j).2
                * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k) * c j) = 0 from
            Finset.sum_eq_zero fun k _ =>
              Finset.sum_eq_zero fun j _ => by
                rw [hLsnd, Q'.form_zero_left]
                ring]
          rw [zero_add]
          calc ∑ k, ∑ j,
              Q'.form (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).2
                (bb j).2
              * c (Fin.natAdd (Module.finrank ℤ Q.Λ) k) * c j
              = ∑ k, ∑ l, Q'.gram b' k l
                  * c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)
                  * c (Fin.natAdd (Module.finrank ℤ Q.Λ) l) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Fin.sum_univ_add (f := fun j =>
                  Q'.form (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).2
                    (bb j).2
                  * c (Fin.natAdd (Module.finrank ℤ Q.Λ) k) * c j)]
                rw [show (∑ l,
                      Q'.form (bb (Fin.natAdd (Module.finrank ℤ Q.Λ) k)).2
                        (bb (Fin.castAdd (Module.finrank ℤ Q'.Λ) l)).2
                      * c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)
                      * c (Fin.castAdd (Module.finrank ℤ Q'.Λ) l)) = 0 from
                  Finset.sum_eq_zero fun l _ => by
                    rw [hLsnd, hzr']
                    ring]
                rw [zero_add]
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [hRsnd, hRsnd, gram_apply]
            _ = _ := quadForm_dotProduct (Q'.gram b') _
        -- one of the two half-vectors is nonzero
        have hcase : (fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k))
              ≠ (0 : Fin (Module.finrank ℤ Q.Λ) → ℝ)
            ∨ (fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k))
              ≠ (0 : Fin (Module.finrank ℤ Q'.Λ) → ℝ) := by
          by_contra hboth
          push Not at hboth
          exact hc (funext fun i => Fin.addCases
            (fun k => congrFun hboth.1 k) (fun k => congrFun hboth.2 k) i)
        have hnn1 : 0 ≤ (fun k =>
              c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)) ⬝ᵥ
            (Q.gram b).mulVec
              (fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k)) := by
          have h := (Q.gram_posDef b).posSemidef.dotProduct_mulVec_nonneg
            (fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k))
          rwa [show star (fun k =>
              c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k))
            = fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k) from
            funext fun k => star_trivial _] at h
        have hnn2 : 0 ≤ (fun k =>
              c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)) ⬝ᵥ
            (Q'.gram b').mulVec
              (fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k)) := by
          have h := (Q'.gram_posDef b').posSemidef.dotProduct_mulVec_nonneg
            (fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k))
          rwa [show star (fun k =>
              c (Fin.natAdd (Module.finrank ℤ Q.Λ) k))
            = fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k) from
            funext fun k => star_trivial _] at h
        rw [hexpand, hA, hB]
        rcases hcase with h | h
        · have hpos := (posDef_iff_dotProduct_mulVec.mp
            (Q.gram_posDef b)).2 h
          rw [show star (fun k =>
              c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k))
            = fun k => c (Fin.castAdd (Module.finrank ℤ Q'.Λ) k) from
            funext fun k => star_trivial _] at hpos
          linarith
        · have hpos := (posDef_iff_dotProduct_mulVec.mp
            (Q'.gram_posDef b')).2 h
          rw [show star (fun k =>
              c (Fin.natAdd (Module.finrank ℤ Q.Λ) k))
            = fun k => c (Fin.natAdd (Module.finrank ℤ Q.Λ) k) from
            funext fun k => star_trivial _] at hpos
          linarith }

@[simp] theorem orthSum_form (p p' : Q.Λ × Q'.Λ) :
    (orthSum Q Q').form p p' = Q.form p.1 p'.1 + Q'.form p.2 p'.2 :=
  rfl

/-- The partition function of any lattice action is positive at
positive coupling — through any Gram chart. -/
theorem scaledPartFn_pos (Q : QuadLatticeAction.{u}) {β : ℝ}
    (hβ : 0 < β) : 0 < Q.scaledPartFn β := by
  rw [Q.scaledPartFn_eq_gramTheta (Module.finBasis ℤ Q.Λ)]
  exact gramTheta_pos (Q.gram_posDef _) hβ

/-- **Partition functions multiply**: the Boltzmann sum of an
orthogonal sum factorizes over its summands. -/
theorem orthSum_scaledPartFn {β : ℝ} (hβ : 0 < β) :
    (orthSum Q Q').scaledPartFn β
      = Q.scaledPartFn β * Q'.scaledPartFn β := by
  have hsum : Summable fun a : Q.Λ => Real.exp (-(β * Q.form a a)) :=
    (Q.scale β hβ).summable
  have hsum' : Summable fun a : Q'.Λ =>
      Real.exp (-(β * Q'.form a a)) := (Q'.scale β hβ).summable
  have hn : Summable fun a : Q.Λ =>
      ‖Real.exp (-(β * Q.form a a))‖ :=
    hsum.congr fun a =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  have hn' : Summable fun a : Q'.Λ =>
      ‖Real.exp (-(β * Q'.form a a))‖ :=
    hsum'.congr fun a =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  unfold scaledPartFn
  rw [tsum_mul_tsum_of_summable_norm hn hn']
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  show -(β * (Q.form p.1 p.1 + Q'.form p.2 p.2)) = _
  ring

/-- **Defects add**: the intrinsic defect of an orthogonal sum is
the sum of the factors' defects — description costs add across
orthogonal factors. -/
theorem orthSum_defect {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    (orthSum Q Q').defect s q q'
      = Q.defect s q q' + Q'.defect s q q' := by
  unfold QuadLatticeAction.defect
  rw [fieldDefect_congr
    (fun β hβ => orthSum_scaledPartFn Q Q' hβ) hs hq hq']
  exact fieldDefect_mul (fun β hβ => Q.scaledPartFn_pos hβ)
    (fun β hβ => Q'.scaledPartFn_pos hβ) hs hq hq'

/-- **The vanishing biconditional**: since every factor's defect is
nonpositive, the defect of an orthogonal sum vanishes iff the
defect of every factor vanishes — any zero-defect witness descends
past every orthogonal decomposition. -/
theorem orthSum_defect_eq_zero_iff {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    (orthSum Q Q').defect s q q' = 0
      ↔ Q.defect s q q' = 0 ∧ Q'.defect s q q' = 0 := by
  rw [orthSum_defect Q Q' hs hq hq']
  have h1 := Q.defect_nonpos hs hq hq'
  have h2 := Q'.defect_nonpos hs hq hq'
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, add_zero]

/-- **Strict rectangle inequalities are preserved by orthogonal
sums**: if both factors satisfy the strict rectangle inequality at
`t, a, b`, so does their orthogonal sum — partition functions
multiply, and strict inequalities between positive reals
multiply. -/
theorem orthSum_rect_strict {t a b : ℝ} (ht : 0 < t) (ha : 1 < a)
    (hb : 1 < b)
    (h : Q.scaledPartFn (a ^ 2 * t) * Q.scaledPartFn (b ^ 2 * t)
      < Q.scaledPartFn t * Q.scaledPartFn ((a * b) ^ 2 * t))
    (h' : Q'.scaledPartFn (a ^ 2 * t) * Q'.scaledPartFn (b ^ 2 * t)
      < Q'.scaledPartFn t * Q'.scaledPartFn ((a * b) ^ 2 * t)) :
    (orthSum Q Q').scaledPartFn (a ^ 2 * t)
        * (orthSum Q Q').scaledPartFn (b ^ 2 * t)
      < (orthSum Q Q').scaledPartFn t
        * (orthSum Q Q').scaledPartFn ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have h1 : (0 : ℝ) < a ^ 2 * t := by positivity
  have h2 : (0 : ℝ) < b ^ 2 * t := by positivity
  have h3 : (0 : ℝ) < (a * b) ^ 2 * t := by positivity
  rw [orthSum_scaledPartFn Q Q' h1, orthSum_scaledPartFn Q Q' h2,
    orthSum_scaledPartFn Q Q' ht, orthSum_scaledPartFn Q Q' h3]
  calc Q.scaledPartFn (a ^ 2 * t) * Q'.scaledPartFn (a ^ 2 * t)
      * (Q.scaledPartFn (b ^ 2 * t) * Q'.scaledPartFn (b ^ 2 * t))
      = (Q.scaledPartFn (a ^ 2 * t) * Q.scaledPartFn (b ^ 2 * t))
        * (Q'.scaledPartFn (a ^ 2 * t)
          * Q'.scaledPartFn (b ^ 2 * t)) := by ring
    _ < (Q.scaledPartFn t * Q.scaledPartFn ((a * b) ^ 2 * t))
        * (Q'.scaledPartFn t
          * Q'.scaledPartFn ((a * b) ^ 2 * t)) :=
        mul_lt_mul'' h h'
          (mul_nonneg (Q.scaledPartFn_pos h1).le
            (Q.scaledPartFn_pos h2).le)
          (mul_nonneg (Q'.scaledPartFn_pos h1).le
            (Q'.scaledPartFn_pos h2).le)
    _ = Q.scaledPartFn t * Q'.scaledPartFn t
        * (Q.scaledPartFn ((a * b) ^ 2 * t)
          * Q'.scaledPartFn ((a * b) ^ 2 * t)) := by ring

/-- **Counterexample descent**: a failure of the strict rectangle
inequality on an orthogonal sum is a failure on one of the
factors — any strictness counterexample descends through every
orthogonal decomposition. -/
theorem rect_strict_descend {t a b : ℝ} (ht : 0 < t) (ha : 1 < a)
    (hb : 1 < b)
    (hfail : ¬ ((orthSum Q Q').scaledPartFn (a ^ 2 * t)
        * (orthSum Q Q').scaledPartFn (b ^ 2 * t)
      < (orthSum Q Q').scaledPartFn t
        * (orthSum Q Q').scaledPartFn ((a * b) ^ 2 * t))) :
    ¬ (Q.scaledPartFn (a ^ 2 * t) * Q.scaledPartFn (b ^ 2 * t)
        < Q.scaledPartFn t * Q.scaledPartFn ((a * b) ^ 2 * t))
    ∨ ¬ (Q'.scaledPartFn (a ^ 2 * t) * Q'.scaledPartFn (b ^ 2 * t)
        < Q'.scaledPartFn t * Q'.scaledPartFn ((a * b) ^ 2 * t)) := by
  by_contra hboth
  push Not at hboth
  exact hfail (orthSum_rect_strict Q Q' ht ha hb hboth.1 hboth.2)

end QuadLatticeAction

end Theaetetus
