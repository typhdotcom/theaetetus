import Theaetetus.LogConvexity
import Theaetetus.LargeScale
import Descent.Core.Field
import Descent.Core.Defect
import Descent.Core.Higher
import Descent.Models.Diamond
import Mathlib.GroupTheory.Index

/-! # The Gaussian diamond

Every corrected higher defect of a pairwise coprime family
telescopes into pairwise defects: on the divisibility carrier the
order-separated hierarchy carries no information beyond order two.
That collapse is a consequence of distributivity. This module
exhibits the opposite case, and exhibits it geometrically.

The carrier here is the lattice of subgroups of `ℤ²`, meet the
intersection and join the sum. Inside it the five sublattices

    2ℤ² ≤ {a even}, {b even}, {a + b even} ≤ ℤ²

form a copy of the diamond: distinct atoms intersect in `2ℤ²` and
sum to `ℤ²` (`inf_evenFst_evenSnd` and its companions), so the
realization is a lattice homomorphism out of the abstract diamond
(`diamondHom`) and a faithful one (`diamondSub_injective`). The
carrier is modular and not distributive, and the failure is
visible: the sum of the two meets against the checkerboard is
`2ℤ²`, while the meet of the sum is the checkerboard itself
(`distrib_interval`).

The field is intrinsic. Each sublattice is priced by the logarithm
of its own convergent Gaussian mass, the Boltzmann sum of the
squared euclidean length over its points (`latMass`, `latMass_pos`,
`latField`). Each mass is evaluated by parametrizing the sublattice
by `ℤ²` — the doubling `(u, v) ↦ (2u, 2v)`, the two half-doublings,
and the parity rotation `(u, v) ↦ (u + v, u − v)`, whose energy is
`2(u² + v²)`:

    ρ(ℤ²) = θ(s)²,           ρ(2ℤ²) = θ(4s)²,
    ρ({a even}) = ρ({b even}) = θ(s)·θ(4s),
    ρ({a + b even}) = θ(2s)².

The pairwise calibration is exact. The two coordinate sublattices
split the ambient lattice orthogonally and their defect vanishes
(`defect_evenFst_evenSnd`); each of them against the checkerboard
has defect `2·log θ(2s) − log θ(s) − log θ(4s)`, strictly negative
at every positive scale by the strict midpoint inequality at ratio
`√2` (`defect_evenFst_evenSum_neg`, `defect_evenSnd_evenSum_neg`).
Every pairwise observation on this five-point carrier is therefore
nonpositive (`defect_diamondHom_nonpos`), the comparable pairs
vanishing by the chain law. The vanishing atom pair is a
coincidence of masses forced by an
orthogonal splitting; it is no counterexample to
`defect_neg_of_incomparable`, whose carrier is the divisibility
lattice of scalar dilations, not the subgroup lattice of `ℤ²`.

The order-3 defect is nevertheless strictly positive. The exact
order-3 recurrence kills all three of its pairwise terms — the
coordinate pair has no defect, the join of that pair is the whole
lattice and so comparable with the checkerboard, and both meets
with the checkerboard are `2ℤ²` — and leaves exactly the field gap
across the distributivity-defect interval (`defect3_diamond`):

    D₃ = log ρ({a + b even}) − log ρ(2ℤ²) = 2·log(θ(2s)/θ(4s)) > 0

(`defect3_diamond_eq`, `defect3_diamond_pos`), read on the abstract
diamond through the realization by `defect3_diamondHom`. Order-3
information is genuinely new on this carrier, and it survives the
boundary: as the scale falls to zero the duality leaves the ratio
of the two scaling prefactors and the theta factors saturate at
`1`, so `D₃ → log 2` (`tendsto_defect3_diamond`).

That limit is an index. Each atom has index two in `ℤ²`
(`index_evenFst`, `index_evenSnd`, `index_evenSum`), and the
doubled lattice has index two inside the checkerboard
(`relIndex_evenBoth_evenSum`) — the two ends of the
distributivity-defect interval — so the boundary value is the
logarithm of that relative index
(`tendsto_defect3_diamond_index`). -/

namespace Theaetetus

/-! ## The five sublattices -/

/-- The index-two sublattice of `ℤ²` cut out by evenness of the
first coordinate. -/
def evenFst : AddSubgroup (ℤ × ℤ) where
  carrier := {v | Even v.1}
  zero_mem' := Even.zero
  add_mem' ha hb := Even.add ha hb
  neg_mem' ha := Even.neg ha

/-- The index-two sublattice of `ℤ²` cut out by evenness of the
second coordinate. -/
def evenSnd : AddSubgroup (ℤ × ℤ) where
  carrier := {v | Even v.2}
  zero_mem' := Even.zero
  add_mem' ha hb := Even.add ha hb
  neg_mem' ha := Even.neg ha

/-- The index-two sublattice of `ℤ²` cut out by evenness of the
coordinate sum. -/
def evenSum : AddSubgroup (ℤ × ℤ) where
  carrier := {v | Even (v.1 + v.2)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have h := Even.add ha hb
    show Even (a.1 + b.1 + (a.2 + b.2))
    rw [show a.1 + b.1 + (a.2 + b.2) = a.1 + a.2 + (b.1 + b.2) by ring]
    exact h
  neg_mem' := by
    intro a ha
    show Even (-a.1 + -a.2)
    rw [show -a.1 + -a.2 = -(a.1 + a.2) by ring]
    exact Even.neg ha

/-- The doubled lattice `2ℤ²`: both coordinates even. -/
def evenBoth : AddSubgroup (ℤ × ℤ) where
  carrier := {v | Even v.1 ∧ Even v.2}
  zero_mem' := ⟨Even.zero, Even.zero⟩
  add_mem' ha hb := ⟨Even.add ha.1 hb.1, Even.add ha.2 hb.2⟩
  neg_mem' ha := ⟨Even.neg ha.1, Even.neg ha.2⟩

@[simp] theorem mem_evenFst {v : ℤ × ℤ} : v ∈ evenFst ↔ Even v.1 := Iff.rfl

@[simp] theorem mem_evenSnd {v : ℤ × ℤ} : v ∈ evenSnd ↔ Even v.2 := Iff.rfl

@[simp] theorem mem_evenSum {v : ℤ × ℤ} :
    v ∈ evenSum ↔ Even (v.1 + v.2) := Iff.rfl

@[simp] theorem mem_evenBoth {v : ℤ × ℤ} :
    v ∈ evenBoth ↔ Even v.1 ∧ Even v.2 := Iff.rfl


/-! ## The meet and join table -/


private theorem evenBoth_le_evenFst : evenBoth ≤ evenFst :=
  SetLike.le_def.mpr fun _ h => (mem_evenBoth.mp h).1

private theorem evenBoth_le_evenSnd : evenBoth ≤ evenSnd :=
  SetLike.le_def.mpr fun _ h => (mem_evenBoth.mp h).2

private theorem evenBoth_le_evenSum : evenBoth ≤ evenSum :=
  SetLike.le_def.mpr fun v h => by
    simp only [mem_evenBoth, Int.even_iff] at h
    simp only [mem_evenSum, Int.even_iff]
    omega

theorem inf_evenFst_evenSnd : evenFst ⊓ evenSnd = evenBoth := by
  refine SetLike.ext fun v => ?_
  simp [AddSubgroup.mem_inf]

theorem inf_evenFst_evenSum : evenFst ⊓ evenSum = evenBoth := by
  refine SetLike.ext fun v => ?_
  simp only [AddSubgroup.mem_inf, mem_evenFst, mem_evenSum, mem_evenBoth,
    Int.even_iff]
  omega

theorem inf_evenSnd_evenSum : evenSnd ⊓ evenSum = evenBoth := by
  refine SetLike.ext fun v => ?_
  simp only [AddSubgroup.mem_inf, mem_evenSnd, mem_evenSum, mem_evenBoth,
    Int.even_iff]
  omega

theorem sup_evenFst_evenSnd : evenFst ⊔ evenSnd = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).mpr fun v => ?_
  have h1 : ((0 : ℤ), v.2) ∈ evenFst ⊔ evenSnd :=
    SetLike.le_def.mp le_sup_left (show Even ((0 : ℤ), v.2).1 from Even.zero)
  have h2 : (v.1, (0 : ℤ)) ∈ evenFst ⊔ evenSnd :=
    SetLike.le_def.mp le_sup_right (show Even (v.1, (0 : ℤ)).2 from Even.zero)
  have hv : v = ((0 : ℤ), v.2) + (v.1, (0 : ℤ)) :=
    Prod.ext_iff.mpr ⟨by simp, by simp⟩
  rw [hv]
  exact add_mem h1 h2

theorem sup_evenFst_evenSum : evenFst ⊔ evenSum = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).mpr fun v => ?_
  have h1 : ((0 : ℤ), v.2 - v.1) ∈ evenFst ⊔ evenSum :=
    SetLike.le_def.mp le_sup_left
      (show Even ((0 : ℤ), v.2 - v.1).1 from Even.zero)
  have h2 : (v.1, v.1) ∈ evenFst ⊔ evenSum :=
    SetLike.le_def.mp le_sup_right
      (show Even ((v.1, v.1).1 + (v.1, v.1).2) from ⟨v.1, rfl⟩)
  have hv : v = ((0 : ℤ), v.2 - v.1) + (v.1, v.1) :=
    Prod.ext_iff.mpr ⟨by simp, by simp⟩
  rw [hv]
  exact add_mem h1 h2

theorem sup_evenSnd_evenSum : evenSnd ⊔ evenSum = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).mpr fun v => ?_
  have h1 : (v.1 - v.2, (0 : ℤ)) ∈ evenSnd ⊔ evenSum :=
    SetLike.le_def.mp le_sup_left
      (show Even (v.1 - v.2, (0 : ℤ)).2 from Even.zero)
  have h2 : (v.2, v.2) ∈ evenSnd ⊔ evenSum :=
    SetLike.le_def.mp le_sup_right
      (show Even ((v.2, v.2).1 + (v.2, v.2).2) from ⟨v.2, rfl⟩)
  have hv : v = (v.1 - v.2, (0 : ℤ)) + (v.2, v.2) :=
    Prod.ext_iff.mpr ⟨by simp, by simp⟩
  rw [hv]
  exact add_mem h1 h2

/-! ## The diamond of sublattices -/

/-- The five sublattices as a map out of the abstract diamond:
`2ℤ²` at the bottom, the three index-two sublattices as atoms, and
`ℤ²` at the top. -/
def diamondSub : Descent.Diamond → AddSubgroup (ℤ × ℤ)
  | .bot => evenBoth
  | .x => evenSnd
  | .y => evenFst
  | .z => evenSum
  | .top => ⊤

private theorem diamond_inf_eq (p q : Descent.Diamond) :
    p ⊓ q = Descent.Diamond.infD p q := rfl

private theorem diamond_sup_eq (p q : Descent.Diamond) :
    p ⊔ q = Descent.Diamond.supD p q := rfl

/-- **The geometric realization of the diamond**: meets are
intersections, joins are sums, distinct atoms meet at `2ℤ²` and
join to `ℤ²`. -/
def diamondHom : LatticeHom Descent.Diamond (AddSubgroup (ℤ × ℤ)) where
  toFun := diamondSub
  map_inf' p q := by
    cases p <;> cases q <;>
      simp +decide only [diamond_inf_eq, Descent.Diamond.infD, diamondSub,
        reduceIte, inf_idem, inf_top_eq, top_inf_eq,
        inf_evenFst_evenSnd, inf_evenFst_evenSum, inf_evenSnd_evenSum,
        (inf_comm evenSnd evenFst).trans inf_evenFst_evenSnd,
        (inf_comm evenSum evenFst).trans inf_evenFst_evenSum,
        (inf_comm evenSum evenSnd).trans inf_evenSnd_evenSum,
        inf_of_le_left evenBoth_le_evenFst,
        inf_of_le_right evenBoth_le_evenFst,
        inf_of_le_left evenBoth_le_evenSnd,
        inf_of_le_right evenBoth_le_evenSnd,
        inf_of_le_left evenBoth_le_evenSum,
        inf_of_le_right evenBoth_le_evenSum]
  map_sup' p q := by
    cases p <;> cases q <;>
      simp +decide only [diamond_sup_eq, Descent.Diamond.supD, diamondSub,
        reduceIte, sup_idem, sup_top_eq, top_sup_eq,
        sup_evenFst_evenSnd, sup_evenFst_evenSum, sup_evenSnd_evenSum,
        (sup_comm evenSnd evenFst).trans sup_evenFst_evenSnd,
        (sup_comm evenSum evenFst).trans sup_evenFst_evenSum,
        (sup_comm evenSum evenSnd).trans sup_evenSnd_evenSum,
        sup_of_le_left evenBoth_le_evenFst,
        sup_of_le_right evenBoth_le_evenFst,
        sup_of_le_left evenBoth_le_evenSnd,
        sup_of_le_right evenBoth_le_evenSnd,
        sup_of_le_left evenBoth_le_evenSum,
        sup_of_le_right evenBoth_le_evenSum]

@[simp] theorem diamondHom_apply (p : Descent.Diamond) :
    diamondHom p = diamondSub p := rfl

/-- The realization is faithful: the five sublattices are distinct,
so the diamond embeds in the subgroup lattice of `ℤ²`. -/
theorem diamondSub_injective : Function.Injective diamondSub := by
  intro p q h
  have h10 := SetLike.ext_iff.mp h ((1 : ℤ), (0 : ℤ))
  have h01 := SetLike.ext_iff.mp h ((0 : ℤ), (1 : ℤ))
  have h11 := SetLike.ext_iff.mp h ((1 : ℤ), (1 : ℤ))
  cases p <;> cases q <;>
    first
      | rfl
      | simp [diamondSub, Int.even_iff] at h10 h01 h11

/-! ## The Gaussian mass of a sublattice -/

/-- The Gaussian mass of a sublattice of `ℤ²` at scale `s`: the
Boltzmann sum of the squared euclidean length over its points. -/
noncomputable def latMass (s : ℝ) (H : AddSubgroup (ℤ × ℤ)) : ℝ :=
  ∑' v : H,
    Real.exp (-s * (((v : ℤ × ℤ).1 : ℝ) ^ 2 + ((v : ℤ × ℤ).2 : ℝ) ^ 2))

theorem summable_gaussPair {s : ℝ} (hs : 0 < s) :
    Summable fun p : ℤ × ℤ =>
      Real.exp (-s * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  refine ((summable_theta s hs).mul_of_nonneg (summable_theta s hs)
    (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

theorem summable_latMass {s : ℝ} (hs : 0 < s) (H : AddSubgroup (ℤ × ℤ)) :
    Summable fun v : H =>
      Real.exp (-s * (((v : ℤ × ℤ).1 : ℝ) ^ 2 + ((v : ℤ × ℤ).2 : ℝ) ^ 2)) :=
  (summable_gaussPair hs).subtype (· ∈ H)

/-- **The mass is positive**: the sum converges and its vacuum term
is `1`, so every logarithmic rewrite below is legitimate. -/
theorem latMass_pos {s : ℝ} (hs : 0 < s) (H : AddSubgroup (ℤ × ℤ)) :
    0 < latMass s H :=
  (summable_latMass hs H).tsum_pos (fun _ => (Real.exp_pos _).le) 0
    (Real.exp_pos _)

/-- A parametrization of a sublattice by `ℤ²` transports its mass to
a sum over `ℤ²`. -/
private theorem latMass_param (s : ℝ) {H : AddSubgroup (ℤ × ℤ)}
    (f : ℤ × ℤ → ℤ × ℤ) (hmem : ∀ p, f p ∈ H) (hinj : Function.Injective f)
    (hsurj : ∀ v ∈ H, ∃ p, f p = v) :
    latMass s H
      = ∑' p : ℤ × ℤ,
          Real.exp (-s * (((f p).1 : ℝ) ^ 2 + ((f p).2 : ℝ) ^ 2)) := by
  have hbij : Function.Bijective fun p => (⟨f p, hmem p⟩ : H) := by
    refine ⟨fun p q h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨v, hv⟩
    obtain ⟨p, rfl⟩ := hsurj v hv
    exact ⟨p, rfl⟩
  exact ((Equiv.ofBijective _ hbij).tsum_eq
    (fun v : H =>
      Real.exp
        (-s * (((v : ℤ × ℤ).1 : ℝ) ^ 2 + ((v : ℤ × ℤ).2 : ℝ) ^ 2)))).symm

/-- A diagonal Gaussian sum over `ℤ²` is a product of theta values. -/
private theorem tsum_gauss_pair {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∑' p : ℤ × ℤ,
        Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-d * (p.2 : ℝ) ^ 2))
      = theta c * theta d := by
  have hn : Summable fun k : ℤ => ‖Real.exp (-c * (k : ℝ) ^ 2)‖ :=
    (summable_theta c hc).congr fun k =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  have hn' : Summable fun k : ℤ => ‖Real.exp (-d * (k : ℝ) ^ 2)‖ :=
    (summable_theta d hd).congr fun k =>
      (Real.norm_eq_abs _ ▸ abs_of_nonneg (Real.exp_pos _).le).symm
  rw [← tsum_mul_tsum_of_summable_norm hn hn']
  rfl

/-- The mass of a parametrized sublattice whose energy is diagonal in
the parameters. -/
private theorem latMass_eq_theta_mul (s : ℝ) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) {H : AddSubgroup (ℤ × ℤ)} (f : ℤ × ℤ → ℤ × ℤ)
    (hmem : ∀ p, f p ∈ H)
    (hinj : Function.Injective f) (hsurj : ∀ v ∈ H, ∃ p, f p = v)
    (hquad : ∀ p : ℤ × ℤ,
      s * ((((f p).1 : ℤ) : ℝ) ^ 2 + (((f p).2 : ℤ) : ℝ) ^ 2)
        = c * (p.1 : ℝ) ^ 2 + d * (p.2 : ℝ) ^ 2) :
    latMass s H = theta c * theta d := by
  rw [latMass_param s f hmem hinj hsurj, ← tsum_gauss_pair hc hd]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  rw [show -c * (p.1 : ℝ) ^ 2 + -d * (p.2 : ℝ) ^ 2
      = -(c * (p.1 : ℝ) ^ 2 + d * (p.2 : ℝ) ^ 2) by ring, ← hquad p]
  ring

/-! ## The mass table -/

/-- The full lattice `ℤ²` carries the squared theta mass. -/
theorem latMass_top {s : ℝ} (hs : 0 < s) : latMass s ⊤ = theta s ^ 2 := by
  rw [pow_two]
  refine latMass_eq_theta_mul s hs hs (fun p => p)
    (fun p => AddSubgroup.mem_top p) (fun _ _ h => h)
    (fun v _ => ⟨v, rfl⟩) fun p => by ring

/-- The doubled lattice `2ℤ²` carries the squared theta mass at four
times the scale. -/
theorem latMass_evenBoth {s : ℝ} (hs : 0 < s) :
    latMass s evenBoth = theta (4 * s) ^ 2 := by
  have hs4 : (0 : ℝ) < 4 * s := by linarith
  rw [pow_two]
  refine latMass_eq_theta_mul s hs4 hs4 (fun p => (2 * p.1, 2 * p.2))
    (fun p => ⟨⟨p.1, by ring⟩, ⟨p.2, by ring⟩⟩) ?_ ?_
    fun p => by push_cast; ring
  · intro p q h
    simp only [Prod.ext_iff] at h ⊢
    omega
  · rintro v hv
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := mem_evenBoth.mp hv
    refine ⟨(a, b), Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show (2 * a : ℤ) = v.1
      omega
    · show (2 * b : ℤ) = v.2
      omega

/-- The sublattice with even second coordinate splits into a free and
a doubled direction. -/
theorem latMass_evenSnd {s : ℝ} (hs : 0 < s) :
    latMass s evenSnd = theta s * theta (4 * s) := by
  have hs4 : (0 : ℝ) < 4 * s := by linarith
  refine latMass_eq_theta_mul s hs hs4 (fun p => (p.1, 2 * p.2))
    (fun p => ⟨p.2, by ring⟩) ?_ ?_ fun p => by push_cast; ring
  · intro p q h
    simp only [Prod.ext_iff] at h ⊢
    omega
  · rintro v hv
    obtain ⟨b, hb⟩ := mem_evenSnd.mp hv
    refine ⟨(v.1, b), Prod.ext_iff.mpr ⟨rfl, ?_⟩⟩
    show (2 * b : ℤ) = v.2
    omega

/-- The sublattice with even first coordinate carries the same mass:
the two coordinate sublattices are isometric. -/
theorem latMass_evenFst {s : ℝ} (hs : 0 < s) :
    latMass s evenFst = theta s * theta (4 * s) := by
  have hs4 : (0 : ℝ) < 4 * s := by linarith
  rw [mul_comm]
  refine latMass_eq_theta_mul s hs4 hs (fun p => (2 * p.1, p.2))
    (fun p => ⟨p.1, by ring⟩) ?_ ?_ fun p => by push_cast; ring
  · intro p q h
    simp only [Prod.ext_iff] at h ⊢
    omega
  · rintro v hv
    obtain ⟨a, ha⟩ := mem_evenFst.mp hv
    refine ⟨(a, v.2), Prod.ext_iff.mpr ⟨?_, rfl⟩⟩
    show (2 * a : ℤ) = v.1
    omega

/-- The checkerboard sublattice is the doubled lattice rotated: the
parity parametrization `(u, v) ↦ (u + v, u − v)` has energy
`2(u² + v²)`, so its mass is the squared theta mass at twice the
scale. -/
theorem latMass_evenSum {s : ℝ} (hs : 0 < s) :
    latMass s evenSum = theta (2 * s) ^ 2 := by
  have hs2 : (0 : ℝ) < 2 * s := by linarith
  rw [pow_two]
  refine latMass_eq_theta_mul s hs2 hs2 (fun p => (p.1 + p.2, p.1 - p.2))
    (fun p => ⟨p.1, by ring⟩) ?_ ?_ fun p => by push_cast; ring
  · intro p q h
    simp only [Prod.ext_iff] at h ⊢
    omega
  · rintro v hv
    obtain ⟨a, ha⟩ := mem_evenSum.mp hv
    refine ⟨(a, v.1 - a), Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show (a + (v.1 - a) : ℤ) = v.1
      omega
    · show (a - (v.1 - a) : ℤ) = v.2
      omega

/-! ## The logarithmic field and its pairwise calibration -/

/-- The logarithmic Gaussian field on the sublattices of `ℤ²`: each
sublattice is priced by the logarithm of its Gaussian mass. -/
noncomputable def latField (s : ℝ) :
    Descent.ContextField (AddSubgroup (ℤ × ℤ)) ℝ :=
  fun H => Real.log (latMass s H)

/-- **The zero of the diamond**: the two coordinate sublattices meet
at `2ℤ²` and join to `ℤ²` with no defect — they split the ambient
lattice orthogonally, so their masses factor through the same pair of
one-dimensional sums. -/
theorem defect_evenFst_evenSnd {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSnd = 0 := by
  have h4 : (0 : ℝ) < 4 * s := by linarith
  simp only [Descent.defect_def, latField, inf_evenFst_evenSnd,
    sup_evenFst_evenSnd, latMass_evenFst hs, latMass_evenSnd hs,
    latMass_evenBoth hs, latMass_top hs, Real.log_pow,
    Real.log_mul (theta_pos s hs).ne' (theta_pos _ h4).ne']
  push_cast
  ring

/-- The defect of a coordinate sublattice against the checkerboard. -/
theorem defect_evenFst_evenSum {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSum
      = 2 * Real.log (theta (2 * s)) - Real.log (theta s)
        - Real.log (theta (4 * s)) := by
  have h4 : (0 : ℝ) < 4 * s := by linarith
  simp only [Descent.defect_def, latField, inf_evenFst_evenSum,
    sup_evenFst_evenSum, latMass_evenFst hs, latMass_evenSum hs,
    latMass_evenBoth hs, latMass_top hs, Real.log_pow,
    Real.log_mul (theta_pos s hs).ne' (theta_pos _ h4).ne']
  push_cast
  ring

/-- The other coordinate sublattice pairs with the checkerboard
identically. -/
theorem defect_evenSnd_evenSum {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenSnd evenSum
      = 2 * Real.log (theta (2 * s)) - Real.log (theta s)
        - Real.log (theta (4 * s)) := by
  have h4 : (0 : ℝ) < 4 * s := by linarith
  simp only [Descent.defect_def, latField, inf_evenSnd_evenSum,
    sup_evenSnd_evenSum, latMass_evenSnd hs, latMass_evenSum hs,
    latMass_evenBoth hs, latMass_top hs, Real.log_pow,
    Real.log_mul (theta_pos s hs).ne' (theta_pos _ h4).ne']
  push_cast
  ring

/-- The strict midpoint inequality at ratio `√2`: the checkerboard
mass is strictly submultiplicative against the two coordinate
sublattices. -/
theorem theta_two_sq_lt {s : ℝ} (hs : 0 < s) :
    theta (2 * s) ^ 2 < theta s * theta (4 * s) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have h := theta_sq_lt hs h1
  rwa [hsq, show Real.sqrt 2 ^ 4 = 4 by nlinarith] at h

/-- **The strict pair**: a coordinate sublattice and the checkerboard
are incomparable, and their defect is strictly negative at every
positive scale. -/
theorem defect_evenFst_evenSum_neg {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSum < 0 := by
  have h4 : (0 : ℝ) < 4 * s := by linarith
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have hlog :=
    Real.log_lt_log (pow_pos (theta_pos _ h2) 2) (theta_two_sq_lt hs)
  rw [Real.log_pow,
    Real.log_mul (theta_pos s hs).ne' (theta_pos _ h4).ne'] at hlog
  rw [defect_evenFst_evenSum hs]
  push_cast at hlog
  linarith

/-- The two coordinate sublattices pair with the checkerboard
identically: their defects against it agree. -/
theorem defect_evenFst_evenSum_eq_evenSnd {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSum
      = Descent.defect (latField s) evenSnd evenSum := by
  rw [defect_evenFst_evenSum hs, defect_evenSnd_evenSum hs]

/-- The same strict sign for the other coordinate sublattice. -/
theorem defect_evenSnd_evenSum_neg {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenSnd evenSum < 0 := by
  rw [defect_evenSnd_evenSum hs, ← defect_evenFst_evenSum hs]
  exact defect_evenFst_evenSum_neg hs

/-- **All pairwise observations vanish or fall**: on the realized
diamond every pairwise defect is nonpositive — zero on the
comparable pairs and on the orthogonal coordinate pair, strictly
negative on the two pairs that meet a coordinate sublattice with
the checkerboard. -/
theorem defect_diamondHom_nonpos {s : ℝ} (hs : 0 < s)
    (p q : Descent.Diamond) :
    Descent.defect (latField s ∘ diamondHom) p q ≤ 0 := by
  have hcomp : ∀ a b : AddSubgroup (ℤ × ℤ), a ≤ b ∨ b ≤ a →
      Descent.defect (latField s) a b ≤ 0 := by
    rintro a b (h | h)
    · exact le_of_eq (Descent.defect_of_le _ h)
    · exact le_of_eq
        ((Descent.defect_comm _ _ _).trans (Descent.defect_of_le _ h))
  have hFS : Descent.defect (latField s) evenFst evenSnd ≤ 0 :=
    le_of_eq (defect_evenFst_evenSnd hs)
  have hSF : Descent.defect (latField s) evenSnd evenFst ≤ 0 :=
    le_of_eq ((Descent.defect_comm _ _ _).trans (defect_evenFst_evenSnd hs))
  have hFU : Descent.defect (latField s) evenFst evenSum ≤ 0 :=
    (defect_evenFst_evenSum_neg hs).le
  have hUF : Descent.defect (latField s) evenSum evenFst ≤ 0 :=
    (Descent.defect_comm _ _ _).le.trans hFU
  have hSU : Descent.defect (latField s) evenSnd evenSum ≤ 0 :=
    (defect_evenSnd_evenSum_neg hs).le
  have hUS : Descent.defect (latField s) evenSum evenSnd ≤ 0 :=
    (Descent.defect_comm _ _ _).le.trans hSU
  rw [Descent.defect_comp diamondHom (latField s)]
  cases p <;> cases q <;>
    simp only [diamondHom_apply, diamondSub] <;>
    first
      | exact hFS
      | exact hSF
      | exact hFU
      | exact hUF
      | exact hSU
      | exact hUS
      | exact hcomp _ _ (Or.inl le_rfl)
      | exact hcomp _ _ (Or.inl le_top)
      | exact hcomp _ _ (Or.inr le_top)
      | exact hcomp _ _ (Or.inl evenBoth_le_evenFst)
      | exact hcomp _ _ (Or.inr evenBoth_le_evenFst)
      | exact hcomp _ _ (Or.inl evenBoth_le_evenSnd)
      | exact hcomp _ _ (Or.inr evenBoth_le_evenSnd)
      | exact hcomp _ _ (Or.inl evenBoth_le_evenSum)
      | exact hcomp _ _ (Or.inr evenBoth_le_evenSum)

/-! ## The irreducible third order -/

/-- **The field gap is the whole third order**: on the atom triple
the exact order-3 recurrence kills its three pairwise terms — the
coordinate pair has no defect, the join of that pair is the whole
lattice and so comparable with the checkerboard, and both meets with
the checkerboard are `2ℤ²` — leaving exactly the field gap across the
distributivity-defect interval `[2ℤ², L]` between the sum of the
meets and the meet of the sum. -/
theorem defect3_diamond {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s) evenFst evenSnd evenSum
      = latField s evenSum - latField s evenBoth := by
  rw [Descent.defect3_recurrence, defect_evenFst_evenSnd hs,
    sup_evenFst_evenSnd, inf_evenFst_evenSum, inf_evenSnd_evenSum,
    Descent.defect_comm (latField s) ⊤ evenSum,
    Descent.defect_of_le (latField s) (le_top : evenSum ≤ ⊤),
    Descent.defect_self, top_inf_eq, sup_idem]
  ring

/-- The interval carrying the gap: the sum of the two meets is `2ℤ²`,
the meet of the sum is the checkerboard itself. -/
theorem distrib_interval :
    (evenFst ⊓ evenSum) ⊔ (evenSnd ⊓ evenSum) = evenBoth
      ∧ (evenFst ⊔ evenSnd) ⊓ evenSum = evenSum := by
  refine ⟨?_, ?_⟩
  · rw [inf_evenFst_evenSum, inf_evenSnd_evenSum, sup_idem]
  · rw [sup_evenFst_evenSnd, top_inf_eq]

/-- **The third-order identity**: the diamond's order-3 defect is the
logarithm of the mass ratio between the checkerboard sublattice and
the doubled lattice. -/
theorem defect3_diamond_eq {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s) evenFst evenSnd evenSum
      = 2 * Real.log (theta (2 * s) / theta (4 * s)) := by
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have h4 : (0 : ℝ) < 4 * s := by linarith
  rw [defect3_diamond hs]
  simp only [latField, latMass_evenSum hs, latMass_evenBoth hs, Real.log_pow,
    Real.log_div (theta_pos _ h2).ne' (theta_pos _ h4).ne']
  push_cast
  ring

/-- **The sign of the diamond**: the order-3 defect is strictly
positive at every positive scale — the pairwise data is nonpositive,
the third-order datum is not. -/
theorem defect3_diamond_pos {s : ℝ} (hs : 0 < s) :
    0 < Descent.defect3 (latField s) evenFst evenSnd evenSum := by
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have h4 : (0 : ℝ) < 4 * s := by linarith
  rw [defect3_diamond_eq hs]
  have hlt : theta (4 * s) < theta (2 * s) := theta_lt_theta h2 (by linarith)
  have h1 : 1 < theta (2 * s) / theta (4 * s) :=
    (one_lt_div (theta_pos _ h4)).mpr hlt
  have := Real.log_pos h1
  linarith

/-- The order-3 defect read on the abstract diamond through the
geometric realization. -/
theorem defect3_diamondHom {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s ∘ diamondHom) Descent.Diamond.x
        Descent.Diamond.y Descent.Diamond.z
      = 2 * Real.log (theta (2 * s) / theta (4 * s)) := by
  rw [Descent.defect3_comp diamondHom (latField s),
    Descent.defect3_comm_left]
  exact defect3_diamond_eq hs

/-! ## The boundary value -/

open Filter Topology in
/-- **The interaction survives the boundary**: as the scale falls to
zero the order-3 defect converges to `log 2`, the logarithm of the
index of the doubled lattice inside the checkerboard sublattice.
The duality supplies the ratio of the two scaling prefactors; the
remaining theta factors saturate at `1`. -/
theorem tendsto_defect3_diamond :
    Tendsto (fun s => Descent.defect3 (latField s) evenFst evenSnd evenSum)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)) := by
  have hlog : ∀ t : ℝ, 0 < t → Real.log (theta t)
      = 1 / 2 * Real.log (Real.pi / t)
        + Real.log (theta (Real.pi ^ 2 / t)) := by
    intro t ht
    have hα : 0 < Real.pi ^ 2 / t := by positivity
    have hd := theta_duality_real (Real.pi ^ 2 / t) hα
    rw [show Real.pi ^ 2 / (Real.pi ^ 2 / t) = t by field_simp] at hd
    rw [hd, show Real.pi ^ 2 / t / Real.pi = Real.pi / t by field_simp,
      Real.log_mul (by positivity) (theta_pos _ hα).ne',
      Real.log_rpow (by positivity)]
  have hratio : ∀ s : ℝ, 0 < s →
      Real.log (Real.pi / (2 * s)) - Real.log (Real.pi / (4 * s))
        = Real.log 2 := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    rw [show Real.pi / (2 * s) = 2 * (Real.pi / (4 * s)) by field_simp; ring,
      Real.log_mul (by norm_num) (by positivity)]
    ring
  have key : ∀ s : ℝ, 0 < s →
      Real.log 2 + 2 * (Real.log (theta (Real.pi ^ 2 / (2 * s)))
          - Real.log (theta (Real.pi ^ 2 / (4 * s))))
        = Descent.defect3 (latField s) evenFst evenSnd evenSum := by
    intro s hs
    have h2 : (0 : ℝ) < 2 * s := by linarith
    have h4 : (0 : ℝ) < 4 * s := by linarith
    rw [defect3_diamond_eq hs,
      Real.log_div (theta_pos _ h2).ne' (theta_pos _ h4).ne',
      hlog (2 * s) h2, hlog (4 * s) h4, ← hratio s hs]
    ring
  have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hscale : ∀ c : ℝ, 0 < c →
      Tendsto (fun s : ℝ => Real.log (theta (Real.pi ^ 2 / (c * s))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro c hc
    have hdiv : Tendsto (fun s : ℝ => Real.pi ^ 2 / (c * s))
        (𝓝[>] (0 : ℝ)) atTop := by
      refine (Tendsto.const_mul_atTop (r := Real.pi ^ 2 / c)
        (by positivity) hinv).congr' ?_
      refine eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => ?_
      have hs0 : s ≠ 0 := ne_of_gt hs
      field_simp
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp
      (tendsto_theta_atTop.comp hdiv)
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun s : ℝ => Real.log 2
      + 2 * (Real.log (theta (Real.pi ^ 2 / (2 * s)))
        - Real.log (theta (Real.pi ^ 2 / (4 * s)))))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)) := by
    have h := (tendsto_const_nhds (x := Real.log 2) (f := 𝓝[>] (0 : ℝ))).add
      (((hscale 2 (by norm_num)).sub (hscale 4 (by norm_num))).const_mul 2)
    simpa using h
  exact hlim.congr'
    (eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => key s hs)

/-! ## The index reading -/

/-- The sublattice with even first coordinate has index two. -/
theorem index_evenFst : evenFst.index = 2 := by
  rw [AddSubgroup.index_eq_two_iff]
  refine ⟨((1 : ℤ), (0 : ℤ)), fun b => ?_⟩
  show Xor (Even (b.1 + 1)) (Even b.1)
  simp only [Xor, Int.even_iff]
  omega

/-- The sublattice with even second coordinate has index two. -/
theorem index_evenSnd : evenSnd.index = 2 := by
  rw [AddSubgroup.index_eq_two_iff]
  refine ⟨((0 : ℤ), (1 : ℤ)), fun b => ?_⟩
  show Xor (Even (b.2 + 1)) (Even b.2)
  simp only [Xor, Int.even_iff]
  omega

/-- The checkerboard sublattice has index two. -/
theorem index_evenSum : evenSum.index = 2 := by
  rw [AddSubgroup.index_eq_two_iff]
  refine ⟨((1 : ℤ), (0 : ℤ)), fun b => ?_⟩
  show Xor (Even (b.1 + 1 + (b.2 + 0))) (Even (b.1 + b.2))
  simp only [Xor, Int.even_iff]
  omega

/-- **The relative index**: the doubled lattice sits inside the
checkerboard sublattice with index two. -/
theorem relIndex_evenBoth_evenSum : evenBoth.relIndex evenSum = 2 := by
  have hmem : ((1 : ℤ), (1 : ℤ)) ∈ evenSum := ⟨1, rfl⟩
  show (evenBoth.addSubgroupOf evenSum).index = 2
  rw [AddSubgroup.index_eq_two_iff]
  refine ⟨⟨((1 : ℤ), (1 : ℤ)), hmem⟩, ?_⟩
  rintro ⟨v, hv⟩
  rw [mem_evenSum, Int.even_iff] at hv
  show Xor (Even (v.1 + 1) ∧ Even (v.2 + 1)) (Even v.1 ∧ Even v.2)
  simp only [Xor, Int.even_iff]
  omega

open Filter Topology in
/-- **The boundary value is an index**: the small-scale limit of the
order-3 defect is the logarithm of the index of the doubled lattice
inside the checkerboard sublattice, the two ends of the
distributivity-defect interval. -/
theorem tendsto_defect3_diamond_index :
    Tendsto (fun s => Descent.defect3 (latField s) evenFst evenSnd evenSum)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((evenBoth.relIndex evenSum : ℕ) : ℝ))) := by
  rw [relIndex_evenBoth_evenSum]
  simpa using tendsto_defect3_diamond

end Theaetetus
