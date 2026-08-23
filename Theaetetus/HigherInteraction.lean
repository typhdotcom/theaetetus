import Theaetetus.Submodular
import Theaetetus.Correlation
import Descent.Core.Field
import Descent.Core.Defect
import Descent.Core.Hierarchy
import Descent.Models.Arithmetic

/-! # The arithmetic realization of the abstract defect

The abstract order-separated defect calculus — context fields on a
lattice, the pairwise defect `K a + K b − K (a ⊓ b) − K (a ⊔ b)`,
and its corrected higher orders — lives in the `Descent` library
and is not restated here. This module identifies the arithmetic
realization: a partition field `Z : ℝ → ℝ` at a fixed scale `s`
induces the logarithmic context field `q ↦ log Z(q²·s)` on the
carrier of positive naturals under divisibility (`logField`), and
the four-term defect of `Z` over the resolution rectangle
`{q, q′, gcd, lcm}` is exactly the abstract pairwise defect of
that field (`fieldDefect_eq_defect`): meet and join on the carrier
are `gcd` and `lcm`, so the resolution rectangle is the comparison
square. Every law of `fieldDefect` transports across this
identification, and every abstract law of `Descent.defect`
specializes to partition fields.

On a pairwise coprime family of resolutions the abstract
inclusion–exclusion defect of every arity telescopes into pairwise
defects (`defectFam_logField_eq_telescope`): coprimality collapses
the meet-translated subfamily of the recurrence to the trivial
resolution and annihilates the distributivity-gap remainder, so
peeling one entry costs exactly the pairwise defect of that entry
against the product of the others. The recursion follows the
abstract recurrence and so eliminates from the front, pricing each
entry against the product of those following it; because its value
is the symmetric abstract defect, it does not depend on that
presentation (`telescope_eq_of_perm`), and every elimination order
gives the same total. At arity three that coherence reads
`D(a,b) + D(ab,c) = D(b,c) + D(a,bc)`. The telescope is a
reorganization, not a vanishing theorem: at rank one every
corrected order of a nontrivial coprime family is strictly
negative (`defectFam_theta_neg`), and for every positive-definite
lattice action it is nonpositive
(`QuadLatticeAction.defectFam_nonpos`). Raw mixed differences of
the field are a different object and are not treated here. -/

namespace Theaetetus

/-- The fixed-scale logarithmic context field of a partition
field: each positive-natural resolution is priced by the
log-partition value at its squared coupling. -/
noncomputable def logField (Z : ℝ → ℝ) (s : ℝ) :
    Descent.ContextField Descent.Arith ℝ :=
  fun a => Real.log (Z (((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s))

/-- **The arithmetic defect bridge**: the four-term defect of a
partition field over the resolution rectangle `{q, q′, gcd, lcm}`
is the abstract pairwise defect of its logarithmic context field
on the carrier of positive naturals under divisibility — meet is
`gcd`, join is `lcm`, and the resolution rectangle is the
comparison square. -/
theorem fieldDefect_eq_defect (Z : ℝ → ℝ) (s : ℝ) (n m : ℕ+) :
    fieldDefect Z s (n : ℕ) (m : ℕ)
      = Descent.defect (logField Z s)
          (Descent.Arith.of n) (Descent.Arith.of m) := by
  have hn : (Descent.Arith.num (Descent.Arith.of n) : ℕ) = (n : ℕ) := rfl
  have hm : (Descent.Arith.num (Descent.Arith.of m) : ℕ) = (m : ℕ) := rfl
  have hinf : (Descent.Arith.num
        (Descent.Arith.of n ⊓ Descent.Arith.of m) : ℕ)
      = Nat.gcd (n : ℕ) (m : ℕ) :=
    Descent.Arith.num_inf (Descent.Arith.of n) (Descent.Arith.of m)
  have hsup : (Descent.Arith.num
        (Descent.Arith.of n ⊔ Descent.Arith.of m) : ℕ)
      = Nat.lcm (n : ℕ) (m : ℕ) :=
    Descent.Arith.num_sup (Descent.Arith.of n) (Descent.Arith.of m)
  rw [Descent.defect_def]
  unfold logField fieldDefect
  rw [hn, hm, hinf, hsup]
  ring

/-! ## Coprime families and the telescope -/

/-- The product of a nonempty family of resolutions: the head
carries the empty product. -/
def prodFam (n : ℕ+) (l : List ℕ+) : ℕ+ :=
  l.foldr (· * ·) n

@[simp] theorem prodFam_nil (n : ℕ+) : prodFam n [] = n := rfl

theorem prodFam_cons (n m : ℕ+) (l : List ℕ+) :
    prodFam n (m :: l) = m * prodFam n l := rfl

/-- A family of resolutions whose entries are pairwise coprime. -/
def PairwiseCoprime (l : List ℕ+) : Prop :=
  l.Pairwise fun x y : ℕ+ => Nat.Coprime (x : ℕ) (y : ℕ)

/-- Contexts of the arithmetic carrier are equal when their
resolutions are. -/
private theorem arith_ext {a b : Descent.Arith}
    (h : (Descent.Arith.num a : ℕ) = (Descent.Arith.num b : ℕ)) : a = b :=
  PNat.coe_injective h

/-- A resolution coprime to every entry of a family is coprime to
their product. -/
private theorem coprime_prodFam {d a : ℕ+} {l : List ℕ+}
    (h : ∀ x ∈ a :: l, Nat.Coprime (d : ℕ) (x : ℕ)) :
    Nat.Coprime (d : ℕ) ((prodFam a l : ℕ+) : ℕ) := by
  induction l with
  | nil => exact h a (List.mem_cons_self ..)
  | cons b t ih =>
      rw [prodFam_cons, PNat.mul_coe]
      refine Nat.Coprime.mul_right
        (h b (List.mem_cons_of_mem a (List.mem_cons_self ..)))
        (ih fun x hx => ?_)
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h x (List.mem_cons_self ..)
      · exact h x (List.mem_cons_of_mem a (List.mem_cons_of_mem b hx'))

/-- A nontrivial head makes the whole product nontrivial. -/
private theorem one_lt_prodFam {a : ℕ+} (ha : 1 < (a : ℕ)) (l : List ℕ+) :
    1 < ((prodFam a l : ℕ+) : ℕ) := by
  induction l with
  | nil => exact ha
  | cons b t ih =>
      rw [prodFam_cons, PNat.mul_coe]
      calc 1 < ((prodFam a t : ℕ+) : ℕ) := ih
        _ ≤ (b : ℕ) * ((prodFam a t : ℕ+) : ℕ) :=
            Nat.le_mul_of_pos_left _ b.pos

/-- **A coprime family joins to its product**: on the arithmetic
carrier the join of a pairwise coprime family is the product of its
entries. -/
theorem supFam_of_pairwiseCoprime {a : ℕ+} {l : List ℕ+}
    (h : PairwiseCoprime (a :: l)) :
    Descent.supFam (Descent.Arith.of a) (l.map Descent.Arith.of)
      = Descent.Arith.of (prodFam a l) := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      have hhead := (List.pairwise_cons.mp h).1
      have htail := (List.pairwise_cons.mp h).2
      have hbt := (List.pairwise_cons.mp htail).1
      have hat : PairwiseCoprime (a :: t) :=
        List.pairwise_cons.mpr
          ⟨fun x hx => hhead x (List.mem_cons_of_mem b hx),
            (List.pairwise_cons.mp htail).2⟩
      have hbp : Nat.Coprime ((b : ℕ+) : ℕ) ((prodFam a t : ℕ+) : ℕ) := by
        refine coprime_prodFam (a := a) (l := t) fun x hx => ?_
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact (hhead b (List.mem_cons_self ..)).symm
        · exact hbt x hx'
      rw [List.map_cons, Descent.supFam_cons, ih hat]
      refine arith_ext ?_
      rw [Descent.Arith.num_sup]
      show Nat.lcm ((b : ℕ+) : ℕ) ((prodFam a t : ℕ+) : ℕ)
        = ((prodFam a (b :: t) : ℕ+) : ℕ)
      rw [hbp.lcm_eq_mul, prodFam_cons, PNat.mul_coe]

/-- **The coprime peeling step**: on a pairwise coprime family
extended by a coprime resolution, the exact recurrence of the
abstract hierarchy loses both correction terms — the
meet-translated subfamily collapses to the trivial resolution and
the distributivity-gap remainder cancels — leaving one pairwise
defect against the product of the family. -/
theorem defectFam_cons_coprime (K : Descent.ContextField Descent.Arith ℝ)
    (d a : ℕ+) (l : List ℕ+)
    (hd : ∀ x ∈ a :: l, Nat.Coprime (x : ℕ) (d : ℕ))
    (hl : PairwiseCoprime (a :: l)) :
    Descent.defectFam K (Descent.Arith.of d) ((a :: l).map Descent.Arith.of)
      = Descent.defectFam K (Descent.Arith.of a) (l.map Descent.Arith.of)
        + Descent.defect K (Descent.Arith.of (prodFam a l))
            (Descent.Arith.of d) := by
  have hnum : ∀ y : ℕ+, Nat.Coprime (y : ℕ) (d : ℕ) →
      (Descent.Arith.num
        (Descent.Arith.of y ⊓ Descent.Arith.of d) : ℕ) = 1 := by
    intro y hy
    rw [Descent.Arith.num_inf]
    exact hy
  have hprod : Nat.Coprime ((prodFam a l : ℕ+) : ℕ) (d : ℕ) :=
    (coprime_prodFam (d := d) (a := a) (l := l)
      fun x hx => (hd x hx).symm).symm
  have hdom : ∀ x ∈ (l.map Descent.Arith.of).map (· ⊓ Descent.Arith.of d),
      x ≤ Descent.Arith.of a ⊓ Descent.Arith.of d := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    refine Descent.Arith.le_iff_dvd.mpr ?_
    rw [hnum z (hd z (List.mem_cons_of_mem a hz)),
      hnum a (hd a (List.mem_cons_self ..))]
  have hinf : Descent.Arith.of (prodFam a l) ⊓ Descent.Arith.of d
      = Descent.Arith.of a ⊓ Descent.Arith.of d :=
    arith_ext (by rw [hnum _ hprod, hnum a (hd a (List.mem_cons_self ..))])
  rw [List.map_cons, Descent.defectFam_cons, supFam_of_pairwiseCoprime hl,
    Descent.defectFam_of_forall_le hdom, Descent.supFam_of_forall_le hdom,
    hinf]
  ring

/-- The telescoped sum of pairwise defects along a family: each
entry is priced against the product of the entries following it. -/
noncomputable def telescope (Z : ℝ → ℝ) (s : ℝ) : ℕ+ → List ℕ+ → ℝ
  | _, [] => 0
  | d, a :: l =>
      telescope Z s a l
        + fieldDefect Z s ((prodFam a l : ℕ+) : ℕ) ((d : ℕ+) : ℕ)

@[simp] theorem telescope_nil (Z : ℝ → ℝ) (s : ℝ) (d : ℕ+) :
    telescope Z s d [] = 0 := rfl

theorem telescope_cons (Z : ℝ → ℝ) (s : ℝ) (d a : ℕ+) (l : List ℕ+) :
    telescope Z s d (a :: l)
      = telescope Z s a l
        + fieldDefect Z s ((prodFam a l : ℕ+) : ℕ) ((d : ℕ+) : ℕ) := rfl

/-- **The coprime telescope**: on a pairwise coprime family the
abstract inclusion–exclusion defect of a partition field's
logarithmic context field, at every arity, is the sum of the
pairwise field defects of each entry against the product of the
entries following it:

    D_k(q₁,…,q_k) = Σ_{j=1}^{k−1} D(q_j, q_{j+1}⋯q_k). -/
theorem defectFam_logField_eq_telescope (Z : ℝ → ℝ) (s : ℝ)
    (d : ℕ+) (l : List ℕ+) (h : PairwiseCoprime (d :: l)) :
    Descent.defectFam (logField Z s) (Descent.Arith.of d)
        (l.map Descent.Arith.of)
      = telescope Z s d l := by
  induction l generalizing d with
  | nil => simp [Descent.defectFam_nil]
  | cons a t ih =>
      have hhead := (List.pairwise_cons.mp h).1
      have htail := (List.pairwise_cons.mp h).2
      rw [defectFam_cons_coprime _ d a t
        (fun x hx => (hhead x hx).symm) htail, ih a htail,
        telescope_cons, ← fieldDefect_eq_defect]

/-- **The telescope does not see the presentation**: two coprime
families with the same entries have the same telescope, so the
order in which entries are eliminated does not change the total.
The abstract defect of a family is symmetric, and the telescope
computes it. -/
theorem telescope_eq_of_perm (Z : ℝ → ℝ) (s : ℝ) {d d' : ℕ+} {l l' : List ℕ+}
    (hp : (d :: l).Perm (d' :: l')) (h : PairwiseCoprime (d :: l)) :
    telescope Z s d l = telescope Z s d' l' := by
  have h' : PairwiseCoprime (d' :: l') :=
    (hp.pairwise_iff fun hxy => Nat.Coprime.symm hxy).mp h
  rw [← defectFam_logField_eq_telescope Z s d l h,
    ← defectFam_logField_eq_telescope Z s d' l' h',
    Descent.defectFam_perm (logField Z s) (hp.map Descent.Arith.of)]

/-! ## The sign of every corrected order -/

/-- At rank one the telescope of a coprime family is nonpositive at
every positive scale. -/
theorem telescope_theta_nonpos {s : ℝ} (hs : 0 < s) (d : ℕ+) (l : List ℕ+) :
    telescope theta s d l ≤ 0 := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a t ih =>
      rw [telescope_cons]
      have h1 := ih a
      have h2 : fieldDefect theta s ((prodFam a t : ℕ+) : ℕ)
          ((d : ℕ+) : ℕ) ≤ 0 := defect_nonpos hs _ _
      linarith

/-- **The strict rank-one sign at every corrected order**: for a
pairwise coprime family of nontrivial resolutions the abstract
inclusion–exclusion defect of the rank-one log-theta field is
strictly negative at every arity — each peeled entry is
incomparable to the product of the entries following it, so the
telescope is a sum of strictly negative rank-one defects. -/
theorem defectFam_theta_neg {s : ℝ} (hs : 0 < s) {d : ℕ+} {l : List ℕ+}
    (hne : l ≠ []) (h : PairwiseCoprime (d :: l))
    (hnt : ∀ x ∈ d :: l, 1 < (x : ℕ)) :
    Descent.defectFam (logField theta s) (Descent.Arith.of d)
        (l.map Descent.Arith.of) < 0 := by
  rw [defectFam_logField_eq_telescope theta s d l h]
  match l, hne with
  | a :: t, _ =>
      have hhead := (List.pairwise_cons.mp h).1
      have hd1 : 1 < (d : ℕ) := hnt d (List.mem_cons_self ..)
      have ha1 : 1 < (a : ℕ) :=
        hnt a (List.mem_cons_of_mem d (List.mem_cons_self ..))
      have hp1 : 1 < ((prodFam a t : ℕ+) : ℕ) := one_lt_prodFam ha1 t
      have hcop : Nat.Coprime ((prodFam a t : ℕ+) : ℕ) (d : ℕ) :=
        (coprime_prodFam (d := d) (a := a) (l := t)
          fun x hx => hhead x hx).symm
      have hpd : ¬ ((prodFam a t : ℕ+) : ℕ) ∣ (d : ℕ) := by
        intro hdvd
        have h1 : ((prodFam a t : ℕ+) : ℕ) ∣ 1 := by
          have hg := Nat.dvd_gcd (dvd_refl ((prodFam a t : ℕ+) : ℕ)) hdvd
          rwa [hcop] at hg
        have := Nat.dvd_one.mp h1
        omega
      have hdp : ¬ (d : ℕ) ∣ ((prodFam a t : ℕ+) : ℕ) := by
        intro hdvd
        have h1 : (d : ℕ) ∣ 1 := by
          have hg := Nat.dvd_gcd hdvd (dvd_refl (d : ℕ))
          rwa [hcop] at hg
        have := Nat.dvd_one.mp h1
        omega
      have hstrict : fieldDefect theta s ((prodFam a t : ℕ+) : ℕ)
          ((d : ℕ+) : ℕ) < 0 := defect_neg_of_incomparable hs hpd hdp
      have hrest := telescope_theta_nonpos hs a t
      rw [telescope_cons]
      linarith

/-- **The all-lattice sign at every corrected order**: for every
positive-definite lattice action and every pairwise coprime family
of resolutions, the abstract inclusion–exclusion defect of the
log-partition context field is nonpositive at every positive
scale — the telescope is a sum of nonpositive lattice defects. -/
theorem QuadLatticeAction.defectFam_nonpos (Q : QuadLatticeAction.{u})
    {s : ℝ} (hs : 0 < s) (d : ℕ+) (l : List ℕ+)
    (h : PairwiseCoprime (d :: l)) :
    Descent.defectFam (logField Q.scaledPartFn s) (Descent.Arith.of d)
        (l.map Descent.Arith.of) ≤ 0 := by
  rw [defectFam_logField_eq_telescope Q.scaledPartFn s d l h]
  clear h
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a t ih =>
      rw [telescope_cons]
      have h1 := ih a
      have h2 : Q.defect s ((prodFam a t : ℕ+) : ℕ) ((d : ℕ+) : ℕ) ≤ 0 :=
        Q.defect_nonpos hs (prodFam a t).pos d.pos
      have h3 : fieldDefect Q.scaledPartFn s
          ((prodFam a t : ℕ+) : ℕ) ((d : ℕ+) : ℕ) ≤ 0 := h2
      linarith

end Theaetetus
