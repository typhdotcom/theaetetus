import Theaetetus.SectorAction
import Theaetetus.Defect
import Mathlib.Analysis.Normed.Group.Tannery

/-! # The partition tower: the abstract saturation interface

The classification of Euler-factorizable carriers consumes
remarkably little structure. This module isolates it: a **partition
tower** is a sector action with a distinguished modal sector, strictly
positive energy away from it, and a summable Boltzmann weight. From
those three fields alone follow the saturation of the scaled
partition function at infinite inverse temperature
(`tendsto_Z_atTop`), the strict excess of the base sum on a
nontrivial tower (`one_lt_Z`), the staircase limit of the defect
(`tendsto_defect_succ`), **the recovery formula**
(`tendsto_defect_row_sub_succ`): the sampled complexity
`log Z(m²)` is a single limit of differences of defect entries,
`D(m, km+1) − D(k+1, k+2) → log Z(m²)` — and **the
classification** (`defect_forall_eq_zero_iff`): the defect
vanishes identically iff the tower has only its modal sector.

The tower's defect is *defined* by the cross-ratio of scaled
partition functions — the shape that the carrier's cross-ratio law
proves for residue complexities. Instances then inherit the
classification by exhibiting the three fields: rank-one theta is the
instance `thetaTower` (below, with the bridge
`defect_eq_thetaTower_defect`); graph carriers and arbitrary
positive-definite lattice actions instantiate in
`Classification.lean`. -/

namespace Theaetetus

universe u

open Filter Topology

/-- **The partition tower**: a sector action with a distinguished
modal sector, strictly positive energy off it, and (inherited) a
summable Boltzmann weight — the minimal interface the
classification consumes. -/
structure PartitionTower extends SectorAction.{u} where
  /-- The distinguished zero-energy sector. -/
  modal : Λ
  E_modal : E modal = 0
  E_pos : ∀ k, k ≠ modal → 0 < E k

namespace PartitionTower

variable (T : PartitionTower.{u})

/-- The β-scaled partition function of the tower. -/
noncomputable def Z (β : ℝ) : ℝ :=
  ∑' k : T.Λ, Real.exp (-(β * T.E k))

/-- At `β = 1` the scaled sum is the sector action's partition
function. -/
theorem Z_one : T.Z 1 = T.partFn := by
  unfold Z SectorAction.partFn SectorAction.weight
  exact tsum_congr fun k => by rw [one_mul]

/-- Summability of the β-weight for `β ≥ 1`, by comparison at the
base. -/
theorem summable_Z {β : ℝ} (hβ : 1 ≤ β) :
    Summable (fun k : T.Λ => Real.exp (-(β * T.E k))) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (fun k => Real.exp_le_exp.mpr (by nlinarith [T.E_nonneg k]))
    T.summable

/-- The modal sector alone already contributes `1`. -/
theorem one_le_Z {β : ℝ} (hβ : 1 ≤ β) : 1 ≤ T.Z β := by
  have h := (T.summable_Z hβ).le_tsum T.modal (fun _ _ => (Real.exp_pos _).le)
  rwa [T.E_modal, mul_zero, neg_zero, Real.exp_zero] at h

/-- **Strict excess on a nontrivial tower**: any sector besides the
modal one pushes the Boltzmann sum strictly above `1`. -/
theorem one_lt_Z {β : ℝ} (hβ : 1 ≤ β) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    1 < T.Z β := by
  classical
  obtain ⟨k₀, hk₀⟩ := hnt
  have hle : ∀ k : T.Λ,
      (if k = T.modal then (1 : ℝ) else 0) ≤ Real.exp (-(β * T.E k)) := by
    intro k
    by_cases hk : k = T.modal
    · subst hk
      simp [T.E_modal]
    · simp only [if_neg hk]
      exact (Real.exp_pos _).le
  have hstrict : (if k₀ = T.modal then (1 : ℝ) else 0)
      < Real.exp (-(β * T.E k₀)) := by
    rw [if_neg hk₀]
    exact Real.exp_pos _
  calc (1 : ℝ)
      = ∑' k : T.Λ, (if k = T.modal then (1 : ℝ) else 0) :=
        (tsum_ite_eq T.modal (fun _ => (1 : ℝ))).symm
    _ < T.Z β :=
        Summable.tsum_lt_tsum hle hstrict
          ⟨1, hasSum_ite_eq T.modal (1 : ℝ)⟩ (T.summable_Z hβ)

/-- The excess over `1` is the Boltzmann sum off the modal
sector. -/
theorem Z_sub_one {β : ℝ} (hβ : 1 ≤ β) :
    T.Z β - 1
      = ∑' k : {k : T.Λ // k ≠ T.modal}, Real.exp (-(β * T.E k.1)) := by
  have hsplit := (T.summable_Z hβ).tsum_subtype_add_tsum_subtype_compl
    {T.modal}
  rw [tsum_singleton T.modal (fun k => Real.exp (-(β * T.E k))),
    T.E_modal, mul_zero, neg_zero, Real.exp_zero] at hsplit
  have hcompl : (∑' k : ↥(({T.modal} : Set T.Λ)ᶜ),
        Real.exp (-(β * T.E k.1)))
      = ∑' k : {k : T.Λ // k ≠ T.modal}, Real.exp (-(β * T.E k.1)) := rfl
  rw [← hcompl]
  unfold Z
  linarith [hsplit]

/-- **Saturation**: at infinite inverse temperature only the modal
sector survives — dominated convergence against the base weight. -/
theorem tendsto_Z_atTop : Tendsto T.Z atTop (𝓝 1) := by
  classical
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (β : ℝ) (k : T.Λ) => Real.exp (-(β * T.E k)))
    (g := fun k => if k = T.modal then (1 : ℝ) else 0)
    (bound := fun k => Real.exp (-T.E k)) T.summable
    (by
      intro k
      by_cases hk : k = T.modal
      · subst hk
        simp only [T.E_modal, mul_zero, neg_zero, Real.exp_zero, if_pos]
        exact tendsto_const_nhds
      · simp only [if_neg hk]
        have hE : 0 < T.E k := T.E_pos k hk
        have h1 : Tendsto (fun β : ℝ => β * T.E k) atTop atTop :=
          (tendsto_mul_const_atTop_of_pos hE).mpr tendsto_id
        have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
        simpa only [Function.comp_def] using h2)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      intro k
      have hE : 0 ≤ T.E k := T.E_nonneg k
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith)
  rw [tsum_ite_eq T.modal (fun _ => (1 : ℝ))] at hlim
  exact hlim

/-- On a trivial tower every Boltzmann sum collapses to the modal
term. -/
theorem Z_eq_one_of_forall_eq (htriv : ∀ k : T.Λ, k = T.modal) (β : ℝ) :
    T.Z β = 1 := by
  unfold Z
  rw [tsum_eq_single T.modal fun k hk => absurd (htriv k) hk,
    T.E_modal, mul_zero, neg_zero, Real.exp_zero]

/-! ## The defect of the tower -/

/-- **The defect of a partition tower**: the four-term cross-ratio
of scaled partition functions over the divisibility interval
`[gcd, lcm]` — the abstract shape that the carrier's cross-ratio law
instantiates. -/
noncomputable def defect (q q' : ℕ) : ℝ :=
  (Real.log (T.Z ((q : ℝ) ^ 2)) + Real.log (T.Z ((q' : ℝ) ^ 2)))
    - (Real.log (T.Z ((Nat.gcd q q' : ℝ) ^ 2))
      + Real.log (T.Z ((Nat.lcm q q' : ℝ) ^ 2)))

/-- The tower instance of the field defect: the tower defect is the
field defect of the tower's partition function at unit scale. -/
theorem defect_eq_fieldDefect (q q' : ℕ) :
    T.defect q q' = fieldDefect T.Z 1 q q' := by
  unfold defect fieldDefect
  simp only [mul_one]

/-- The tower defect is symmetric in its resolutions — inherited
from the field defect. -/
theorem defect_comm (q q' : ℕ) : T.defect q q' = T.defect q' q := by
  rw [T.defect_eq_fieldDefect, T.defect_eq_fieldDefect]
  exact fieldDefect_comm T.Z 1 q q'

/-- The tower defect vanishes on chains — pure `gcd`/`lcm` algebra,
before any analysis, inherited from the field defect. -/
theorem defect_eq_zero_of_dvd {q q' : ℕ} (hdvd : q ∣ q') :
    T.defect q q' = 0 := by
  rw [T.defect_eq_fieldDefect]
  exact fieldDefect_eq_zero_of_dvd T.Z 1 hdvd

/-- The tower defect vanishes on the diagonal — inherited from the
field defect. -/
theorem defect_self (q : ℕ) : T.defect q q = 0 :=
  T.defect_eq_zero_of_dvd dvd_rfl

private lemma coprime_succ_succ (n : ℕ) : Nat.Coprime (n + 1) (n + 2) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

/-- **Saturation along any escaping resolution sequence**: the
tail complexity `log Z(a(n)²)` vanishes in the limit. -/
theorem tendsto_log_Z_sq {a : ℕ → ℕ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => Real.log (T.Z ((a n : ℝ) ^ 2))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n => ((a n : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ha
  have hsq : Tendsto (fun n => ((a n : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hcast
  have hZ : Tendsto (fun n => T.Z ((a n : ℝ) ^ 2)) atTop (𝓝 1) :=
    T.tendsto_Z_atTop.comp hsq
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hZ
  simpa only [Function.comp_def, Real.log_one] using hlog

/-- **The staircase limit**: along the coprime pairs `(n+1, n+2)`
the tower defect converges to minus the base complexity — three
cross-ratio terms saturate, the shared trivial constraint remains. -/
theorem tendsto_defect_succ :
    Tendsto (fun n : ℕ => T.defect (n + 1) (n + 2)) atTop
      (𝓝 (-Real.log (T.Z 1))) := by
  have hA := T.tendsto_log_Z_sq (tendsto_add_atTop_nat 1)
  have hB := T.tendsto_log_Z_sq (tendsto_add_atTop_nat 2)
  have hL := T.tendsto_log_Z_sq (a := fun n => (n + 1) * (n + 2))
    (tendsto_atTop_mono (fun n => by nlinarith) (tendsto_add_atTop_nat 1))
  have hlaw : ∀ n : ℕ, T.defect (n + 1) (n + 2)
      = (Real.log (T.Z (((n + 1 : ℕ) : ℝ) ^ 2))
          + Real.log (T.Z (((n + 2 : ℕ) : ℝ) ^ 2)))
        - (Real.log (T.Z 1)
          + Real.log (T.Z ((((n + 1) * (n + 2) : ℕ) : ℝ) ^ 2))) := by
    intro n
    unfold defect
    rw [show Nat.gcd (n + 1) (n + 2) = 1 from coprime_succ_succ n,
      Nat.Coprime.lcm_eq_mul (coprime_succ_succ n)]
    norm_num
  simp only [hlaw]
  have hlim := (hA.add hB).sub
    ((tendsto_const_nhds (x := Real.log (T.Z 1))).add hL)
  simpa using hlim

/-- **The recovery row**: along the coprime escape `(m, km+1)` the
tower defect converges to `log Z(m²) − log Z(1)` — the two growing
entries saturate, leaving the sampled complexity against the
trivial shared constraint. -/
theorem tendsto_defect_row (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => T.defect m (k * m + 1)) atTop
      (𝓝 (Real.log (T.Z ((m : ℝ) ^ 2)) - Real.log (T.Z 1))) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hco : ∀ k : ℕ, Nat.Coprime m (k * m + 1) := by
    intro k
    have h := (Nat.coprime_add_mul_right_right m 1 k).mpr
      (Nat.coprime_one_right m)
    rwa [show 1 + k * m = k * m + 1 from Nat.add_comm 1 (k * m)] at h
  have hkle : ∀ k : ℕ, k ≤ k * m + 1 := fun k =>
    le_trans (le_trans (Nat.mul_one k).symm.le
      (Nat.mul_le_mul_left k hm1)) (Nat.le_succ _)
  have hB := T.tendsto_log_Z_sq (a := fun k => k * m + 1)
    (tendsto_atTop_mono hkle tendsto_id)
  have hL := T.tendsto_log_Z_sq (a := fun k => m * (k * m + 1))
    (tendsto_atTop_mono (fun k => le_trans (hkle k)
      (le_trans (Nat.one_mul (k * m + 1)).symm.le
        (Nat.mul_le_mul_right (k * m + 1) hm1))) tendsto_id)
  have hlaw : ∀ k : ℕ, T.defect m (k * m + 1)
      = (Real.log (T.Z ((m : ℝ) ^ 2))
          + Real.log (T.Z (((k * m + 1 : ℕ) : ℝ) ^ 2)))
        - (Real.log (T.Z 1)
          + Real.log (T.Z (((m * (k * m + 1) : ℕ) : ℝ) ^ 2))) := by
    intro k
    unfold defect
    rw [show Nat.gcd m (k * m + 1) = 1 from hco k,
      Nat.Coprime.lcm_eq_mul (hco k)]
    norm_num
  simp only [hlaw]
  have hlim := ((tendsto_const_nhds
      (x := Real.log (T.Z ((m : ℝ) ^ 2)))).add hB).sub
    ((tendsto_const_nhds (x := Real.log (T.Z 1))).add hL)
  simpa using hlim

/-- **THE RECOVERY FORMULA**: the sampled complexity `log Z(m²)`
is recovered from coprime defect entries alone — the escaping row
against the staircase, differences of entries of a single defect
matrix. -/
theorem tendsto_defect_row_sub_succ (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => T.defect m (k * m + 1)
        - T.defect (k + 1) (k + 2)) atTop
      (𝓝 (Real.log (T.Z ((m : ℝ) ^ 2)))) := by
  have h := (T.tendsto_defect_row m hm).sub T.tendsto_defect_succ
  have hval : Real.log (T.Z ((m : ℝ) ^ 2))
      = (Real.log (T.Z ((m : ℝ) ^ 2)) - Real.log (T.Z 1))
        - -Real.log (T.Z 1) := by ring
  rw [hval]
  exact h

/-- **The sign at the saturation end**: on a nontrivial tower the
defect is eventually strictly negative along the staircase. -/
theorem eventually_defect_neg (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    ∀ᶠ n : ℕ in atTop, T.defect (n + 1) (n + 2) < 0 := by
  have hpos : 0 < Real.log (T.Z 1) :=
    Real.log_pos (T.one_lt_Z le_rfl hnt)
  exact T.tendsto_defect_succ.eventually_lt_const (by linarith)

/-- **THE CLASSIFICATION**: the defect of a partition tower vanishes
at every pair of resolutions iff the tower has only its modal
sector. One direction is the staircase limit against the strict
excess of a nontrivial base sum; the other is the collapse of every
Boltzmann sum to the modal term. -/
theorem defect_forall_eq_zero_iff :
    (∀ q q' : ℕ, q ≠ 0 → q' ≠ 0 → T.defect q q' = 0)
      ↔ ∀ k : T.Λ, k = T.modal := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hpos : 0 < Real.log (T.Z 1) :=
      Real.log_pos (T.one_lt_Z le_rfl hne)
    have hlim := T.tendsto_defect_succ
    rw [show (fun n : ℕ => T.defect (n + 1) (n + 2)) = fun _ => 0 from
      funext fun n => h (n + 1) (n + 2) n.succ_ne_zero (n + 1).succ_ne_zero]
      at hlim
    have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
    linarith
  · intro htriv q q' _ _
    unfold defect
    simp only [T.Z_eq_one_of_forall_eq htriv]
    simp

end PartitionTower

/-! ## The rank-one instance: the theta tower -/

/-- **The theta tower**: rank one as a partition tower — sectors
`ℤ`, energy `s·k²`, modal sector `0`. -/
noncomputable def thetaTower (s : ℝ) (hs : 0 < s) : PartitionTower where
  Λ := ℤ
  E k := s * (k : ℝ) ^ 2
  E_zero := ⟨0, by norm_num⟩
  E_nonneg := fun k => by positivity
  summable := by
    refine (summable_theta s hs).congr fun k => ?_
    congr 1
    ring
  modal := 0
  E_modal := by norm_num
  E_pos := fun k hk => by
    have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hk
    positivity

/-- The theta tower's scaled partition function is the theta value
at the scaled coupling. -/
theorem thetaTower_Z (s : ℝ) (hs : 0 < s) (β : ℝ) :
    (thetaTower s hs).Z β = theta (β * s) := by
  unfold PartitionTower.Z theta thetaTower
  exact tsum_congr fun k => by congr 1; ring

/-- **Rank one is an instance**: the rank-one defect is the theta
tower's defect — the seed object of the program lives on the
abstract interface. -/
theorem defect_eq_thetaTower_defect {s : ℝ} (hs : 0 < s) (q q' : ℕ) :
    defect s q q' = (thetaTower s hs).defect q q' := by
  unfold defect PartitionTower.defect
  rw [thetaTower_Z, thetaTower_Z, thetaTower_Z, thetaTower_Z]

/-- **The recovery formula at rank one**: `log θ(m²s)` from
coprime defect entries of the fixed-scale matrix alone — the
instantiated form of `tendsto_defect_row_sub_succ`. -/
theorem tendsto_defect_recovery {s : ℝ} (hs : 0 < s) (m : ℕ)
    (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => defect s m (k * m + 1)
        - defect s (k + 1) (k + 2)) atTop
      (𝓝 (Real.log (theta ((m : ℝ) ^ 2 * s)))) := by
  have h := (thetaTower s hs).tendsto_defect_row_sub_succ m hm
  rw [thetaTower_Z] at h
  refine h.congr fun k => ?_
  rw [← defect_eq_thetaTower_defect hs, ← defect_eq_thetaTower_defect hs]

end Theaetetus
