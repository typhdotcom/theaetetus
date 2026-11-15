import Theaetetus.GramDuality
import Theaetetus.Classification

/-! # Intrinsic defect duality: the lattice and its dual

The Gram chart computes the intrinsic objects. At any integral
basis, the basis-free scaled partition function of a lattice action
is the Gram Boltzmann sum of that basis
(`QuadLatticeAction.scaledPartFn_eq_gramTheta`), so any two charts
agree (`QuadLatticeAction.gramTheta_gram_eq`), the intrinsic defect
(`QuadLatticeAction.defect`, the field defect of `scaledPartFn`) is
computed by every chart (`QuadLatticeAction.defect_eq_gramDefect`),
and two integral bases of the same lattice produce the same Gram
defect (`QuadLatticeAction.gramDefect_gram_eq`). At unit scale the
intrinsic defect is the tower defect
(`QuadLatticeAction.toPartitionTower_defect`).

The dual lattice is intrinsic: the `ℤ`-dual module with the
inverse-Gram pairing (`QuadLatticeAction.dual`), whose chart at the
dual basis is the inverse Gram (`QuadLatticeAction.dual_gram`).
The duality then lands where it belongs: the defect of a lattice
action reflects to the defect of its dual lattice at the reflected
coupling and reduced resolutions
(`QuadLatticeAction.defect_dual`) — `L` and `L*`, not a chart and
its inverse. -/

namespace Theaetetus

open Matrix

universe u

/-- The inverse-Gram pairing collapses at dual-basis vectors: the
dual basis evaluates to Kronecker deltas on the basis. -/
private theorem sum_dual_delta {Λ : Type u} [AddCommGroup Λ]
    [Module ℤ Λ] {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (c : Module.Basis (Fin n) ℤ Λ) (i j : Fin n) :
    (∑ k, ∑ l, G k l * ((c.dualBasis i (c k) : ℤ) : ℝ)
      * ((c.dualBasis j (c l) : ℤ) : ℝ)) = G i j := by
  have houter : ∀ k, k ≠ i → (∑ l, G k l
      * ((c.dualBasis i (c k) : ℤ) : ℝ)
      * ((c.dualBasis j (c l) : ℤ) : ℝ)) = 0 := by
    intro k hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Module.Basis.dualBasis_apply_self, ite_eq_right hk]
    push_cast
    ring
  rw [Fintype.sum_eq_single i houter]
  have hinner : ∀ l, l ≠ j → G i l
      * ((c.dualBasis i (c i) : ℤ) : ℝ)
      * ((c.dualBasis j (c l) : ℤ) : ℝ) = 0 := by
    intro l hl
    rw [Module.Basis.dualBasis_apply_self c j l, ite_eq_right hl]
    push_cast
    ring
  rw [Fintype.sum_eq_single j hinner,
    Module.Basis.dualBasis_apply_self, Module.Basis.dualBasis_apply_self,
    ite_eq_left rfl, ite_eq_left rfl]
  push_cast
  ring

/-- The transition matrices between two integral bases are mutually
inverse: composing the two coordinate expansions returns the
Kronecker delta. -/
private theorem transition_mul {Λ : Type u} [AddCommGroup Λ]
    [Module ℤ Λ] {n m : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (c : Module.Basis (Fin m) ℤ Λ) :
    (Matrix.of fun i k => ((c.repr (b i) k : ℤ) : ℝ))
      * (Matrix.of fun k j => ((b.repr (c k) j : ℤ) : ℝ)) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hexp : (∑ k, b.repr (c k) j * c.repr (b i) k)
      = b.repr (b i) j := b.sum_repr_mul_repr c (b i) j
  rw [Module.Basis.repr_self, Finsupp.single_apply] at hexp
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hexp
  push_cast at hcast
  simp only [Matrix.of_apply]
  rw [← hcast]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

namespace QuadLatticeAction

variable (Q : QuadLatticeAction.{u})

/-- **The chart lemma**: the basis-free scaled partition function
is computed by the Gram chart at any integral basis. -/
theorem scaledPartFn_eq_gramTheta {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ) (β : ℝ) :
    Q.scaledPartFn β = gramTheta (Q.gram b) β := by
  unfold scaledPartFn gramTheta
  rw [← b.equivFun.toEquiv.tsum_eq (fun k : Fin n → ℤ =>
    Real.exp (-β * ∑ i, ∑ j, Q.gram b i j * (k i : ℝ) * (k j : ℝ)))]
  refine tsum_congr fun a => ?_
  show Real.exp (-(β * Q.form a a))
    = Real.exp (-β * ∑ i, ∑ j, Q.gram b i j * ((b.equivFun a i : ℤ) : ℝ)
        * ((b.equivFun a j : ℤ) : ℝ))
  congr 1
  rw [neg_mul, neg_inj, Q.form_repr b a a]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Module.Basis.equivFun_apply, gram_apply]
  ring

/-- **Chart independence of the Boltzmann sum**: any two Gram charts
of the same lattice action compute the same value. -/
theorem gramTheta_gram_eq {n m : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (b' : Module.Basis (Fin m) ℤ Q.Λ) (β : ℝ) :
    gramTheta (Q.gram b) β = gramTheta (Q.gram b') β := by
  rw [← Q.scaledPartFn_eq_gramTheta b, ← Q.scaledPartFn_eq_gramTheta b']

/-- The intrinsic defect of a lattice action: the field defect of
its basis-free scaled partition function. -/
noncomputable def defect (s : ℝ) (q q' : ℕ) : ℝ :=
  fieldDefect Q.scaledPartFn s q q'

/-- Every Gram chart computes the intrinsic defect. -/
theorem defect_eq_gramDefect {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (s : ℝ) (q q' : ℕ) :
    Q.defect s q q' = gramDefect (Q.gram b) s q q' := by
  unfold defect gramDefect fieldDefect
  simp only [Q.scaledPartFn_eq_gramTheta b]

/-- **Basis invariance of the Gram defect**: two integral bases of
the same lattice produce the same Gram defect. -/
theorem gramDefect_gram_eq {n m : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (b' : Module.Basis (Fin m) ℤ Q.Λ) (s : ℝ) (q q' : ℕ) :
    gramDefect (Q.gram b) s q q' = gramDefect (Q.gram b') s q q' := by
  rw [← Q.defect_eq_gramDefect b, ← Q.defect_eq_gramDefect b']

/-- **The tower reading**: the tower defect of a lattice action is
its intrinsic defect at unit scale. -/
theorem toPartitionTower_defect (q q' : ℕ) :
    Q.toPartitionTower.defect q q' = Q.defect 1 q q' := by
  rw [Q.toPartitionTower.defect_eq_fieldDefect]
  rfl

/-- **The intrinsic dual lattice**: the `ℤ`-dual module, carrying
the inverse-Gram pairing of the chosen construction chart. The
choice does not matter: the chart at the dual basis of every
integral basis is the inverse Gram (`dual_gram_at`). -/
noncomputable def dual : QuadLatticeAction.{u} where
  Λ := Module.Dual ℤ Q.Λ
  free := Module.Free.of_basis (Module.finBasis ℤ Q.Λ).dualBasis
  finite := Module.Finite.of_basis (Module.finBasis ℤ Q.Λ).dualBasis
  form φ ψ := ∑ i, ∑ j, (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ i j
      * ((φ (Module.finBasis ℤ Q.Λ i) : ℤ) : ℝ)
      * ((ψ (Module.finBasis ℤ Q.Λ j) : ℤ) : ℝ)
  form_comm φ ψ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have hsymm := (posDef_inv (Q.gram_posDef (Module.finBasis ℤ Q.Λ))).isSymm
    have h : (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ i j
        = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ j i := by
      calc (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ i j
          = ((Q.gram (Module.finBasis ℤ Q.Λ))⁻¹)ᵀ j i := rfl
        _ = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ j i := by rw [hsymm]
    rw [h]
    ring
  form_add_left φ₁ φ₂ ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.add_apply]
    push_cast
    ring
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _
      (Module.finBasis ℤ Q.Λ).dualBasis ?_
    have hmat : (Matrix.of fun i j => ∑ k, ∑ l,
        (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ k l
          * (((Module.finBasis ℤ Q.Λ).dualBasis i
              (Module.finBasis ℤ Q.Λ k) : ℤ) : ℝ)
          * (((Module.finBasis ℤ Q.Λ).dualBasis j
              (Module.finBasis ℤ Q.Λ l) : ℤ) : ℝ))
        = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ := by
      ext i j
      rw [Matrix.of_apply]
      exact sum_dual_delta _ _ i j
    rw [hmat]
    exact posDef_inv (Q.gram_posDef _)

/-- **The dual chart**: the Gram of the dual lattice at the dual
basis of the chosen construction chart is the inverse Gram. -/
theorem dual_gram :
    Q.dual.gram (Module.finBasis ℤ Q.Λ).dualBasis
      = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ := by
  ext i j
  show Q.dual.form ((Module.finBasis ℤ Q.Λ).dualBasis i)
      ((Module.finBasis ℤ Q.Λ).dualBasis j)
    = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ i j
  exact sum_dual_delta _ _ i j

/-- **The dual chart at every basis**: the Gram of the dual lattice
at the dual basis of any integral basis is the inverse Gram — the
basis hidden in the construction of `dual` does not matter. The
integer transition matrices between the two charts are mutually
inverse, and both Grams conjugate through them. -/
theorem dual_gram_at {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.dual.gram b.dualBasis = (Q.gram b)⁻¹ := by
  set c := Module.finBasis ℤ Q.Λ with hcdef
  set P : Matrix (Fin n) (Fin (Module.finrank ℤ Q.Λ)) ℝ :=
    Matrix.of fun i k => ((c.repr (b i) k : ℤ) : ℝ) with hP
  set R : Matrix (Fin (Module.finrank ℤ Q.Λ)) (Fin n) ℝ :=
    Matrix.of fun k j => ((b.repr (c k) j : ℤ) : ℝ) with hR
  have hPR : P * R = 1 := transition_mul b c
  have hRP : R * P = 1 := transition_mul c b
  have hGunit : IsUnit (Q.gram c).det :=
    isUnit_iff_ne_zero.mpr (Q.gram_posDef c).det_pos.ne'
  have hgb : Q.gram b = P * Q.gram c * Pᵀ := by
    ext i j
    rw [gram_apply, Q.form_repr c (b i) (b j), Finset.sum_comm,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply]
    simp only [hP, Matrix.of_apply, gram_apply]
    ring
  have hdb : Q.dual.gram b.dualBasis = Rᵀ * (Q.gram c)⁻¹ * R := by
    ext i j
    show (∑ k, ∑ l, (Q.gram c)⁻¹ k l
        * ((b.dualBasis i (c k) : ℤ) : ℝ)
        * ((b.dualBasis j (c l) : ℤ) : ℝ))
      = (Rᵀ * (Q.gram c)⁻¹ * R) i j
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply, Module.Basis.dualBasis_apply,
      Module.Basis.dualBasis_apply]
    simp only [hR, Matrix.of_apply]
    ring
  have hPtRt : Pᵀ * Rᵀ = 1 := by
    have h := congrArg Matrix.transpose hRP
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at h
  have hmain : Q.gram b * Q.dual.gram b.dualBasis = 1 := by
    rw [hgb, hdb]
    calc P * Q.gram c * Pᵀ * (Rᵀ * (Q.gram c)⁻¹ * R)
        = P * (Q.gram c * ((Pᵀ * Rᵀ) * ((Q.gram c)⁻¹ * R))) := by
          simp only [Matrix.mul_assoc]
      _ = P * (Q.gram c * ((Q.gram c)⁻¹ * R)) := by
          rw [hPtRt, Matrix.one_mul]
      _ = P * (Q.gram c * (Q.gram c)⁻¹ * R) := by
          simp only [Matrix.mul_assoc]
      _ = P * R := by
          rw [Matrix.mul_nonsing_inv _ hGunit, Matrix.one_mul]
      _ = 1 := hPR
  exact (Matrix.inv_eq_right_inv hmain).symm

/-- **Intrinsic higher-rank defect duality**: the defect of a
positive-definite lattice action reflects to the defect of its dual
lattice at the reflected coupling and reduced resolutions — the
lattice and its dual, with every chart weight annihilated. -/
theorem defect_dual {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    Q.defect s q q'
      = Q.dual.defect (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') := by
  rw [Q.defect_eq_gramDefect (Module.finBasis ℤ Q.Λ),
    Q.dual.defect_eq_gramDefect (Module.finBasis ℤ Q.Λ).dualBasis,
    dual_gram]
  exact gramDefect_dual (Q.gram_posDef _) hs hq hq'

end QuadLatticeAction

end Theaetetus
