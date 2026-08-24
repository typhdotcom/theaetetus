import Theaetetus.HigherInteraction
import Theaetetus.OrthogonalSum
import Theaetetus.Pairing
import Theaetetus.Classification
import Descent.Geometry.Kernels

/-! # The resolution metric

The defect measures the correlation slack of a comparison square;
the join kernel of the *normalized* field measures distance. On the
carrier of positive naturals under divisibility the normalized
resolution field is `K(q) = −log Z(q²s)` (`resField`): finer
resolutions cost more, so the field is monotone, and its defect is
the negated field defect (`defect_resField`) — nonnegative exactly
when the partition field's is nonpositive.

That sign is the correlation theorem, not a formality. For a
positive-definite lattice action the field defect is nonpositive at
every positive scale (`QuadLatticeAction.defect_nonpos`), so the
normalized field lies in the submodular chamber
(`submodular_resField`) and the abstract chamber geometry supplies
the triangle inequality (`resPseudoMetricSpace`). An arbitrary
partition tower carries no such sign and would not give a
pseudometric; the scope of the two halves is different.

The distance is that join kernel (`resDist`), in closed form
(`resDist_eq`):

    d_s(q, q′) = log ( Z(q²·s)·Z(q′²·s) / Z(lcm(q,q′)²·s)² ).

Separation, by contrast, is generic. On any tower the scaled
partition function strictly decreases in the coupling above the
base, by strict Boltzmann decay at one nonmodal sector
(`PartitionTower.Z_lt_Z`); for a nontrivial lattice action at any
positive scale this gives strict decay
(`QuadLatticeAction.scaledPartFn_lt`), hence a strictly monotone
normalized field (`strictMono_resField`) and a distance vanishing
only on the diagonal (`resDist_eq_zero_iff`). The resolution
carrier is then a metric space (`resMetricSpace`).

Two facts say what the geometry means. On a comparable pair the
join kernel is the cost gap itself (`resDist_of_le`), so a
divisibility chain embeds in the real cost line. And at rank one
the metric reads the pairing: for coprime `p, q` the prime pairing
is the distance from the base to the product, less the distance
between the two (`pairing_eq_resDist_sub`),

    ⟨p, q⟩_s = d_s(1, p·q) − d_s(p, q),

so an incomparable pair sits strictly closer than its full span
(`resDist_lt_resDist_base`), by exactly that pairing. -/

namespace Theaetetus

universe u

/-! ## Strict decay of a lattice action in its coupling -/

private theorem scaledPartFn_scale (Q : QuadLatticeAction.{u}) {β : ℝ}
    (hβ : 0 < β) (γ : ℝ) :
    (Q.scale β hβ).toPartitionTower.Z γ = Q.scaledPartFn (γ * β) := by
  show (∑' a : Q.Λ, Real.exp (-(γ * (β * Q.form a a))))
      = ∑' a : Q.Λ, Real.exp (-(γ * β * Q.form a a))
  exact tsum_congr fun a => by ring_nf

/-- **Decay in the coupling**: the scaled partition function of a
lattice action is antitone on positive couplings. -/
theorem QuadLatticeAction.scaledPartFn_antitone (Q : QuadLatticeAction.{u})
    {β β' : ℝ} (hβ : 0 < β) (hle : β ≤ β') :
    Q.scaledPartFn β' ≤ Q.scaledPartFn β := by
  have hratio : 1 ≤ β' / β := (one_le_div hβ).mpr hle
  have h := (Q.scale β hβ).toPartitionTower.Z_le_Z (le_refl 1) hratio
  rw [scaledPartFn_scale Q hβ, scaledPartFn_scale Q hβ, one_mul,
    div_mul_cancel₀ _ hβ.ne'] at h
  exact h

/-- **Strict decay in the coupling**: on a nontrivial lattice the
scaled partition function strictly decreases, by strict Boltzmann
decay at one nonzero vector. -/
theorem QuadLatticeAction.scaledPartFn_lt (Q : QuadLatticeAction.{u})
    (hnt : ∃ a : Q.Λ, a ≠ 0) {β β' : ℝ} (hβ : 0 < β) (hlt : β < β') :
    Q.scaledPartFn β' < Q.scaledPartFn β := by
  have hratio : 1 < β' / β := (one_lt_div hβ).mpr hlt
  have h := (Q.scale β hβ).toPartitionTower.Z_lt_Z hnt (le_refl 1) hratio
  rw [scaledPartFn_scale Q hβ, scaledPartFn_scale Q hβ, one_mul,
    div_mul_cancel₀ _ hβ.ne'] at h
  exact h

/-! ## The normalized resolution field -/

/-- **The normalized resolution field**: the negated log-partition
value at the squared resolution. Finer resolutions carry more
description cost, so the field is monotone for the divisibility
order, and its defect is the negated field defect. -/
noncomputable def resField (Z : ℝ → ℝ) (s : ℝ) :
    Descent.ContextField Descent.Arith ℝ :=
  -logField Z s

theorem resField_apply (Z : ℝ → ℝ) (s : ℝ) (a : Descent.Arith) :
    resField Z s a
      = -Real.log (Z (((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s)) :=
  rfl

/-- The normalized field carries the negated field defect. -/
theorem defect_resField (Z : ℝ → ℝ) (s : ℝ) (n m : ℕ+) :
    Descent.defect (resField Z s) (Descent.Arith.of n) (Descent.Arith.of m)
      = -fieldDefect Z s (n : ℕ) (m : ℕ) := by
  rw [resField, Descent.defect_neg, fieldDefect_eq_defect]

/-! ## The resolution distance -/

/-- **The resolution distance**: the join kernel of the normalized
resolution field. -/
noncomputable def resDist (Z : ℝ → ℝ) (s : ℝ) (a b : Descent.Arith) : ℝ :=
  Descent.joinKernel (resField Z s) a b

/-- **The closed form**: the distance is the logarithm of the two
partition values over the squared value at their join. -/
theorem resDist_eq (Z : ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hZ : ∀ β, 0 < β → 0 < Z β) (a b : Descent.Arith) :
    resDist Z s a b
      = Real.log
          (Z (((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s)
              * Z (((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s)
            / Z (((Nat.lcm (Descent.Arith.num a : ℕ)
                  (Descent.Arith.num b : ℕ) : ℕ) : ℝ) ^ 2 * s) ^ 2) := by
  have hna : (0 : ℝ) < ((Descent.Arith.num a : ℕ) : ℝ) := by
    exact_mod_cast (Descent.Arith.num a).pos
  have hnb : (0 : ℝ) < ((Descent.Arith.num b : ℕ) : ℝ) := by
    exact_mod_cast (Descent.Arith.num b).pos
  have hnl : (0 : ℝ) < ((Nat.lcm (Descent.Arith.num a : ℕ)
      (Descent.Arith.num b : ℕ) : ℕ) : ℝ) := by
    have : 0 < Nat.lcm (Descent.Arith.num a : ℕ) (Descent.Arith.num b : ℕ) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero
        (Descent.Arith.num_ne_zero a) (Descent.Arith.num_ne_zero b))
    exact_mod_cast this
  have hza : 0 < Z (((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s) :=
    hZ _ (by positivity)
  have hzb : 0 < Z (((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s) :=
    hZ _ (by positivity)
  have hzl : 0 < Z (((Nat.lcm (Descent.Arith.num a : ℕ)
      (Descent.Arith.num b : ℕ) : ℕ) : ℝ) ^ 2 * s) := hZ _ (by positivity)
  rw [resDist, Descent.joinKernel, resField_apply, resField_apply,
    resField_apply, Descent.Arith.num_sup,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hza.ne' hzb.ne', Real.log_pow]
  push_cast
  ring

/-- **Chains are line distances**: on a comparable pair the join
kernel is the cost difference. For the monotone lattice resolution
field, this makes every divisibility chain embed isometrically in
the real cost line. -/
theorem resDist_of_le (Z : ℝ → ℝ) (s : ℝ) {a b : Descent.Arith} (h : a ≤ b) :
    resDist Z s a b = resField Z s b - resField Z s a := by
  rw [resDist, Descent.joinKernel, sup_of_le_right h]
  ring

/-! ## The chamber hypotheses, for lattice actions -/

/-- The normalized field of a lattice action lies in the submodular
chamber: this is the correlation theorem, and it is where the
triangle inequality comes from. -/
theorem submodular_resField (Q : QuadLatticeAction.{u}) {s : ℝ} (hs : 0 < s) :
    Descent.Submodular (resField Q.scaledPartFn s) := by
  intro a b
  have hq : 0 < ((Descent.Arith.num a : ℕ+) : ℕ) := (Descent.Arith.num a).pos
  have hq' : 0 < ((Descent.Arith.num b : ℕ+) : ℕ) := (Descent.Arith.num b).pos
  have h := Q.defect_nonpos hs hq hq'
  have hda : Descent.defect (resField Q.scaledPartFn s) a b
      = -QuadLatticeAction.defect Q s ((Descent.Arith.num a : ℕ+) : ℕ)
          ((Descent.Arith.num b : ℕ+) : ℕ) :=
    defect_resField Q.scaledPartFn s (Descent.Arith.num a)
      (Descent.Arith.num b)
  rw [hda]
  linarith

private theorem resField_le {Q : QuadLatticeAction.{u}} {s : ℝ} (hs : 0 < s)
    {a b : Descent.Arith} (hab : a ≤ b) :
    resField Q.scaledPartFn s a ≤ resField Q.scaledPartFn s b := by
  have hdvd := Descent.Arith.le_iff_dvd.mp hab
  have hna : (0 : ℝ) < ((Descent.Arith.num a : ℕ) : ℝ) := by
    exact_mod_cast (Descent.Arith.num a).pos
  have hle : ((Descent.Arith.num a : ℕ) : ℝ)
      ≤ ((Descent.Arith.num b : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Descent.Arith.num b).pos hdvd
  have hsq : ((Descent.Arith.num a : ℕ) : ℝ) ^ 2
      ≤ ((Descent.Arith.num b : ℕ) : ℝ) ^ 2 := by nlinarith
  have hcoup : ((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s
      ≤ ((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s :=
    mul_le_mul_of_nonneg_right hsq hs.le
  have hZ := Q.scaledPartFn_antitone (by positivity) hcoup
  have hposb : 0 < Q.scaledPartFn (((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s) :=
    Q.scaledPartFn_pos (by positivity)
  have hlog := Real.log_le_log hposb hZ
  simp only [resField_apply]
  linarith

/-- Monotone: coarser resolutions cost less. -/
theorem monotone_resField (Q : QuadLatticeAction.{u}) {s : ℝ} (hs : 0 < s) :
    Monotone (resField Q.scaledPartFn s) := fun _ _ hab => resField_le hs hab

/-- Strictly monotone on a nontrivial lattice: a strictly finer
resolution costs strictly more. -/
theorem strictMono_resField (Q : QuadLatticeAction.{u}) {s : ℝ} (hs : 0 < s)
    (hnt : ∃ x : Q.Λ, x ≠ 0) :
    StrictMono (resField Q.scaledPartFn s) := by
  intro a b hab
  have hdvd := Descent.Arith.le_iff_dvd.mp hab.le
  have hne : (Descent.Arith.num a : ℕ) ≠ (Descent.Arith.num b : ℕ) := by
    intro h
    exact hab.ne (PNat.coe_injective h)
  have hlt : ((Descent.Arith.num a : ℕ) : ℝ)
      < ((Descent.Arith.num b : ℕ) : ℝ) := by
    have : (Descent.Arith.num a : ℕ) < (Descent.Arith.num b : ℕ) :=
      lt_of_le_of_ne (Nat.le_of_dvd (Descent.Arith.num b).pos hdvd) hne
    exact_mod_cast this
  have hna : (0 : ℝ) < ((Descent.Arith.num a : ℕ) : ℝ) := by
    exact_mod_cast (Descent.Arith.num a).pos
  have hsq : ((Descent.Arith.num a : ℕ) : ℝ) ^ 2
      < ((Descent.Arith.num b : ℕ) : ℝ) ^ 2 := by nlinarith
  have hcoup : ((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s
      < ((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s :=
    mul_lt_mul_of_pos_right hsq hs
  have hZ := Q.scaledPartFn_lt hnt (by positivity) hcoup
  have hposb : 0 < Q.scaledPartFn (((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s) :=
    Q.scaledPartFn_pos (by positivity)
  have hlog := Real.log_lt_log hposb hZ
  simp only [resField_apply]
  linarith

/-! ## The metric -/

/-- **The resolution pseudometric**: the join kernel of the
normalized field is a pseudometric on the resolution carrier. Its
triangle inequality is the correlation theorem — an arbitrary
partition tower supplies no such sign, and would not give one. -/
@[instance_reducible]
noncomputable def resPseudoMetricSpace (Q : QuadLatticeAction.{u}) {s : ℝ}
    (hs : 0 < s) : PseudoMetricSpace Descent.Arith :=
  (submodular_resField Q hs).pseudoMetricSpace (monotone_resField Q hs)

/-- **Separation**: on a nontrivial lattice action the distance
vanishes only on the diagonal, by strict decay. -/
theorem resDist_eq_zero_iff (Q : QuadLatticeAction.{u}) {s : ℝ} (hs : 0 < s)
    (hnt : ∃ x : Q.Λ, x ≠ 0) (a b : Descent.Arith) :
    resDist Q.scaledPartFn s a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hmono := monotone_resField Q hs
    have hA : resField Q.scaledPartFn s a
        ≤ resField Q.scaledPartFn s (a ⊔ b) := hmono le_sup_left
    have hB : resField Q.scaledPartFn s b
        ≤ resField Q.scaledPartFn s (a ⊔ b) := hmono le_sup_right
    rw [resDist, Descent.joinKernel] at h
    have hEa : resField Q.scaledPartFn s a
        = resField Q.scaledPartFn s (a ⊔ b) := by linarith
    have hEb : resField Q.scaledPartFn s b
        = resField Q.scaledPartFn s (a ⊔ b) := by linarith
    have hsm := strictMono_resField Q hs hnt
    have ha : a = a ⊔ b := by
      rcases lt_or_eq_of_le (le_sup_left : a ≤ a ⊔ b) with hlt | heq
      · exact absurd hEa (hsm hlt).ne
      · exact heq
    have hb : b = a ⊔ b := by
      rcases lt_or_eq_of_le (le_sup_right : b ≤ a ⊔ b) with hlt | heq
      · exact absurd hEb (hsm hlt).ne
      · exact heq
    exact ha.trans hb.symm
  · rintro rfl
    rw [resDist, Descent.joinKernel_self]

/-- **The resolution metric**: on a nontrivial lattice action the
pseudometric separates, so the resolution carrier is a metric
space. -/
@[instance_reducible]
noncomputable def resMetricSpace (Q : QuadLatticeAction.{u}) {s : ℝ}
    (hs : 0 < s) (hnt : ∃ x : Q.Λ, x ≠ 0) : MetricSpace Descent.Arith :=
  { resPseudoMetricSpace Q hs with
    eq_of_dist_eq_zero := fun {a b} h =>
      (resDist_eq_zero_iff Q hs hnt a b).mp h }

/-! ## The pairing at rank one -/

private theorem num_of (n : ℕ+) :
    Descent.Arith.num (Descent.Arith.of n) = n :=
  rfl

/-- **The pairing is a distance difference**: at rank one and
coprime resolutions the prime pairing is the distance from the base
to the product, less the distance between the two. -/
theorem pairing_eq_resDist_sub (s : ℝ) (p q : ℕ+)
    (hco : Nat.Coprime (p : ℕ) (q : ℕ)) :
    pairing s (p : ℕ) (q : ℕ)
      = resDist theta s (Descent.Arith.of 1) (Descent.Arith.of (p * q))
        - resDist theta s (Descent.Arith.of p) (Descent.Arith.of q) := by
  have h1 : ((Descent.Arith.num
      (Descent.Arith.of 1 ⊔ Descent.Arith.of (p * q)) : ℕ+) : ℕ)
      = ((p : ℕ) * (q : ℕ)) := by
    rw [Descent.Arith.num_sup]
    show Nat.lcm ((1 : ℕ+) : ℕ) (((p * q : ℕ+)) : ℕ) = _
    rw [PNat.mul_coe]
    exact Nat.lcm_one_left _
  have h2 : ((Descent.Arith.num
      (Descent.Arith.of p ⊔ Descent.Arith.of q) : ℕ+) : ℕ)
      = ((p : ℕ) * (q : ℕ)) := by
    rw [Descent.Arith.num_sup]
    show Nat.lcm ((p : ℕ+) : ℕ) ((q : ℕ+) : ℕ) = _
    exact Nat.Coprime.lcm_eq_mul hco
  rw [resDist, resDist, Descent.joinKernel, Descent.joinKernel]
  simp only [resField_apply, h1, h2, num_of]
  show -defect s ((p : ℕ+) : ℕ) ((q : ℕ+) : ℕ) = _
  unfold defect
  rw [Nat.Coprime.gcd_eq_one hco, Nat.Coprime.lcm_eq_mul hco]
  push_cast
  ring

/-- **Incomparable resolutions are strictly closer than their
span**: at rank one the distance between a nontrivial coprime pair
is strictly below the distance from the base to their product, by
exactly the prime pairing. -/
theorem resDist_lt_resDist_base {s : ℝ} (hs : 0 < s) {p q : ℕ+}
    (hco : Nat.Coprime (p : ℕ) (q : ℕ)) (hpq : ¬ ((p : ℕ) ∣ (q : ℕ)))
    (hqp : ¬ ((q : ℕ) ∣ (p : ℕ))) :
    resDist theta s (Descent.Arith.of p) (Descent.Arith.of q)
      < resDist theta s (Descent.Arith.of 1) (Descent.Arith.of (p * q)) := by
  have hpair := pairing_eq_resDist_sub s p q hco
  have hneg := defect_neg_of_incomparable hs hpq hqp
  have hpos : 0 < pairing s ((p : ℕ+) : ℕ) ((q : ℕ+) : ℕ) := by
    rw [pairing]
    linarith
  linarith

end Theaetetus
