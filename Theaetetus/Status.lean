import Theaetetus.Duality
import Theaetetus.Midpoint
import Theaetetus.Factorization
import Theaetetus.RankFunction
import Theaetetus.Classification
import Theaetetus.Peeling
import Theaetetus.LargeScale
import Theaetetus.SmallScale
import Theaetetus.StarObstruction
import Theaetetus.DiagonalCurvature
import Theaetetus.RankTwo

/-! # The manifest

Public statements of this library, restated as compiler-checked
`example`s and grouped by mathematical topic. An `example` proves
and discards: this file adds nothing, but a renamed theorem or a
weakened statement fails the build here, so the tree's public
claims cannot drift silently.

Topics: the theta identification; the cross-ratio law and the
coupling reading; the sign; the classification; the pairing; the
reflection law; the midpoint inequalities; the kernel chambers;
the star obstruction; the derivative bridge, functional equation,
fluctuation, and the strict rectangle; diagonal forms. -/

namespace Theaetetus

open Filter Topology

/-! ## The theta identification -/

example (α : ℝ) : (↑(theta α) : ℂ) = jacobiTheta (quadTau α) :=
  theta_eq_jacobiTheta α

/-! ## The cross-ratio law and the coupling reading -/

example (G : IncidenceGraph) (q q' : ℕ) [NeZero q] [NeZero q'] :
    G.towerDefect q q'
      = (Real.log (G.classScaledPartFn ((q : ℝ) ^ 2))
          + Real.log (G.classScaledPartFn ((q' : ℝ) ^ 2)))
        - (Real.log (G.classScaledPartFn ((Nat.gcd q q' : ℝ) ^ 2))
          + Real.log (G.classScaledPartFn ((Nat.lcm q q' : ℝ) ^ 2))) :=
  G.crossRatio_law q q'

noncomputable example (G : IncidenceGraph) (q q' : ℕ)
    [NeZero q] [NeZero q'] :
    G.H1Reduction (Nat.lcm q q')
      ≃ Pullback
          (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
          (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q'))) :=
  G.h1ReductionCRT q q'

example (s : ℝ) {q : ℕ} (hq : q ≠ 0) :
    resProb s q
      = (∑' j : {j : ℤ // (q : ℤ) ∣ j}, Real.exp (-s * (j : ℝ) ^ 2))
        / theta s :=
  resProb_eq_event_mass s hq

example {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    -defect s q q'
      = Real.log ((resProb s (Nat.lcm q q') / resProb s (Nat.gcd q q'))
          / ((resProb s q / resProb s (Nat.gcd q q'))
            * (resProb s q' / resProb s (Nat.gcd q q')))) :=
  neg_defect_eq_log_assoc hs hq hq'

example {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    (resProb s q / resProb s (Nat.gcd q q'))
        * (resProb s q' / resProb s (Nat.gcd q q'))
      < resProb s (Nat.lcm q q') / resProb s (Nat.gcd q q') :=
  condProb_mul_lt_of_incomparable hs hqq' hq'q

example {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hco : Nat.Coprime a b) :
    resProb s a * resProb s b < resProb s (a * b) :=
  resProb_mul_lt_of_coprime hs ha hb hco

/-! ## The sign -/

example {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    defect s q q' < 0 :=
  defect_neg_of_incomparable hs hqq' hq'q

example {s : ℝ} (hs : 0 < s) {q q' : ℕ} :
    defect s q q' = 0 ↔ q ∣ q' ∨ q' ∣ q :=
  defect_eq_zero_iff hs

example {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    resComplexity s (Nat.gcd q q') + resComplexity s (Nat.lcm q q')
      < resComplexity s q + resComplexity s q' :=
  resComplexity_strictSubmodular hs hqq' hq'q

example {t a b : ℝ} (ht : 0 < t) (ha : 2 ≤ a) (hab : a < b) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t)
      < theta t * theta ((a * b) ^ 2 * t) :=
  theta_prod_lt_general ht ha hab

example {r : ℕ} {c : Fin r → ℝ} {s : ℝ} (hr : r ≠ 0)
    (hc : ∀ i, 0 < c i) (hs : 0 < s) {q q' : ℕ}
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    diagDefect c s q q' < 0 :=
  diagDefect_neg_of_incomparable hr hc hs hqq' hq'q

example {r : ℕ} {c : Fin r → ℝ} {s : ℝ} (hr : r ≠ 0)
    (hc : ∀ i, 0 < c i) (hs : 0 < s) {q q' : ℕ} :
    diagDefect c s q q' = 0 ↔ q ∣ q' ∨ q' ∣ q :=
  diagDefect_eq_zero_iff hr hc hs

example {s : ℝ} (hs : 0 < s) (q q' : ℕ) :
    resComplexity s (Nat.gcd q q') + resComplexity s (Nat.lcm q q')
      ≤ resComplexity s q + resComplexity s q' :=
  resComplexity_submodular hs q q'

example : thetaGraph.towerDefect 2 3 < 0 :=
  thetaGraph_towerDefect_neg

example (s : ℝ) : thetaGraph.classScaledPartFn s = hexTheta s :=
  thetaGraph_classScaledPartFn s

example {s : ℝ} (hs : 0 < s) :
    hexTheta s ≤ theta (s / 3) * theta (s / 4) :=
  hexTheta_le hs

/-! ## The classification, through the partition tower -/

example (T : PartitionTower) :
    (∀ q q' : ℕ, q ≠ 0 → q' ≠ 0 → T.defect q q' = 0)
      ↔ ∀ k : T.Λ, k = T.modal :=
  T.defect_forall_eq_zero_iff

example (T : PartitionTower) : Tendsto T.Z atTop (𝓝 1) :=
  T.tendsto_Z_atTop

example (T : PartitionTower) :
    Tendsto (fun n : ℕ => T.defect (n + 1) (n + 2)) atTop
      (𝓝 (-Real.log (T.Z 1))) :=
  T.tendsto_defect_succ

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    ∀ᶠ n : ℕ in atTop, T.defect (n + 1) (n + 2) < 0 :=
  T.eventually_defect_neg hnt

example {s : ℝ} (hs : 0 < s) (q q' : ℕ) :
    defect s q q' = (thetaTower s hs).defect q q' :=
  defect_eq_thetaTower_defect hs q q'

example (T : PartitionTower) (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => T.defect m (k * m + 1)) atTop
      (𝓝 (Real.log (T.Z ((m : ℝ) ^ 2)) - Real.log (T.Z 1))) :=
  T.tendsto_defect_row m hm

example (T : PartitionTower) (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => T.defect m (k * m + 1)
        - T.defect (k + 1) (k + 2)) atTop
      (𝓝 (Real.log (T.Z ((m : ℝ) ^ 2)))) :=
  T.tendsto_defect_row_sub_succ m hm

example {s : ℝ} (hs : 0 < s) (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => defect s m (k * m + 1)
        - defect s (k + 1) (k + 2)) atTop
      (𝓝 (Real.log (theta ((m : ℝ) ^ 2 * s)))) :=
  tendsto_defect_recovery hs m hm

example (T : PartitionTower) (c : ℝ) :
    {k : T.Λ | k ≠ T.modal ∧ T.E k ≤ c}.Finite :=
  T.finite_energy_le c

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    IsLeast (T.E '' {k | k ≠ T.modal}) T.leastEnergy :=
  T.leastEnergy_isLeast hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    0 < T.leastEnergy :=
  T.leastEnergy_pos hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    0 < T.leastEnergyMult :=
  T.leastEnergyMult_pos hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun β : ℝ => Real.exp (β * T.leastEnergy) * (T.Z β - 1))
      atTop (𝓝 (T.leastEnergyMult : ℝ)) :=
  T.tendsto_exp_mul_Z_sub_one hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun β : ℝ => -Real.log (T.Z β - 1) / β)
      atTop (𝓝 T.leastEnergy) :=
  T.tendsto_neg_log_Z_sub_one_div hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun m : ℕ =>
        -Real.log (T.Z ((m : ℝ) ^ 2) - 1) / (m : ℝ) ^ 2)
      atTop (𝓝 T.leastEnergy) :=
  T.tendsto_leastEnergy_sample hnt

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) :
    Tendsto (fun m : ℕ =>
        Real.exp ((m : ℝ) ^ 2 * T.leastEnergy)
          * (T.Z ((m : ℝ) ^ 2) - 1))
      atTop (𝓝 (T.leastEnergyMult : ℝ)) :=
  T.tendsto_leastEnergyMult_sample hnt

example (G : IncidenceGraph) (q q' : ℕ) [NeZero q] [NeZero q'] :
    G.towerDefect q q' = G.toPartitionTower.defect q q' :=
  G.towerDefect_eq_partitionTower_defect q q'

example (G : IncidenceGraph) :
    (∀ (q q' : ℕ) [NeZero q] [NeZero q'], G.towerDefect q q' = 0)
      ↔ Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  G.towerDefect_forall_eq_zero_iff

noncomputable example (Q : QuadLatticeAction) : PartitionTower :=
  Q.toPartitionTower

/-! ## The prime pairing -/

example {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : 0 < pairing s p q :=
  pairing_pos hs hp hq hne

example {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ × ℕ => pairing s n.1 n.2)
      (atTop ⊓ 𝓟 {n : ℕ × ℕ | Nat.Coprime n.1 n.2})
      (𝓝 (Real.log (theta s))) :=
  tendsto_pairing hs

example {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hco : Nat.Coprime p q) :
    pairing s p q < Real.log (theta s) :=
  pairing_lt_base hs hp hq hco

/-! ## The reflection law -/

example {t t' a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (ht' : t' = Real.pi ^ 2 / ((a * b) ^ 2 * t)) :
    theta (a ^ 2 * t') * theta (b ^ 2 * t')
        * (theta t * theta ((a * b) ^ 2 * t))
      = theta (a ^ 2 * t) * theta (b ^ 2 * t)
        * (theta t' * theta ((a * b) ^ 2 * t')) :=
  theta_rect_dual ht ha hb ht'

example {t t' a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (ht' : t' = Real.pi ^ 2 / ((a * b) ^ 2 * t)) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t)
        < theta t * theta ((a * b) ^ 2 * t)
      ↔ theta (a ^ 2 * t') * theta (b ^ 2 * t')
        < theta t' * theta ((a * b) ^ 2 * t') :=
  theta_rect_lt_iff ht ha hb ht'

example {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    defect s q q' =
      defect (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
        (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  defect_dual hs hq hq'

example {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hco : Nat.Coprime p q) :
    defect s p q
      = defect (Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s)) p q :=
  defect_scale_even hs hp hq hco

/-! ## The midpoint inequalities -/

example {t a : ℝ} (ht : 0 < t) (ha : 2 ≤ a) :
    theta (a ^ 2 * t) ^ 2 ≤ theta t * theta (a ^ 4 * t) :=
  theta_sq_le ht ha

example {t a : ℝ} (ht : 0 < t) (ha : 2 ≤ a) :
    2 * Real.log (theta (a ^ 2 * t))
      ≤ Real.log (theta t) + Real.log (theta (a ^ 4 * t)) :=
  log_theta_midpoint_le ht ha

/-! ## The kernel chambers -/

example {s : ℝ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) {c : ℕ → ℝ}
    (hc : (∑ p ∈ P, c p) = 0) :
    quadFormOn (pairing s) P c
      = (∑ p ∈ P, ∑ q ∈ P, c p * c q
          * Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)))
        - ∑ p ∈ P, c p ^ 2
          * (Real.log (theta s)
            + Real.log (theta (((p : ℝ) * (p : ℝ)) ^ 2 * s))
            - 2 * Real.log (theta ((p : ℝ) ^ 2 * s))) :=
  quadFormOn_pairing_eq hprime hc

example {s : ℝ} (hs : 1 ≤ s) {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    IsCNDOn (pairing s) P :=
  pairing_cnd_large hs hprime

example (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcard : 3 ≤ P.card) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ¬ IsCNDOn (pairing s) P :=
  pairing_not_cnd_small P hprime hcard

example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p < q) (hqr : q < r)
    (hcpq : Nat.Coprime p q) (hcpr : Nat.Coprime p r)
    (hcqr : Nat.Coprime q r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      2 * pairing s p q + 2 * pairing s p r < pairing s q r :=
  pairing_dominates_small hp hpq hqr hcpq hcpr hcqr

example {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hco : Nat.Coprime p q) :
    Tendsto (fun t : ℝ => Real.exp t * pairing t p q) atTop (𝓝 2) :=
  tendsto_exp_mul_pairing hp hq hco

example {ι : Type*} [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsCNDOn K Q) (hPQ : P ⊆ Q) :
    IsCNDOn K P :=
  hQ.subset hPQ

example {ι : Type*} [DecidableEq ι] {K : ι → ι → ℝ}
    {P Q : Finset ι} (hQ : IsPSDOn K Q) (hPQ : P ⊆ Q) :
    IsPSDOn K P :=
  hQ.subset hPQ

/-! ## The star obstruction -/

example (s : ℝ) (p : ℕ) : deficit s p p = Real.log (theta s) :=
  deficit_self s p

example {s : ℝ} {p q : ℕ} (hco : Nat.Coprime p q) :
    deficit s p q
      = Real.log (theta ((p : ℝ) ^ 2 * s))
        + Real.log (theta ((q : ℝ) ^ 2 * s))
        - Real.log (theta (((p : ℝ) * (q : ℝ)) ^ 2 * s)) :=
  deficit_coprime hco

example {s : ℝ} {P : Finset ℕ} {c : ℕ → ℝ}
    (hc : (∑ p ∈ P, c p) = 0) :
    quadFormOn (deficit s) P c = -quadFormOn (pairing s) P c :=
  quadFormOn_deficit_eq_neg hc

example {s : ℝ} {P : Finset ℕ}
    (h : IsPSDOn (deficit s) P) : IsCNDOn (pairing s) P :=
  deficit_psd_implies_cnd h

example {s : ℝ} (hs : 0 < s) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p)
      ∧ ¬ IsPSDOn (deficit s) P :=
  deficit_not_psd hs

example {s : ℝ} (hs : 1 ≤ s) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p)
      ∧ IsCNDOn (pairing s) P ∧ ¬ IsPSDOn (deficit s) P :=
  cnd_not_psd hs

/-! ## The derivative bridge, the functional equation, the
fluctuation inequality, and the strict rectangle -/

example {α : ℝ} (hα : 0 < α) : HasDerivAt theta (thetaDeriv α) α :=
  hasDerivAt_theta hα

example {α : ℝ} (hα : 0 < α) :
    HasDerivAt thetaDeriv (thetaDeriv2 α) α :=
  hasDerivAt_thetaDeriv hα

example {α : ℝ} (hα : 0 < α) :
    α * (thetaDeriv α / theta α)
      + Real.pi ^ 2 / α
        * (thetaDeriv (Real.pi ^ 2 / α) / theta (Real.pi ^ 2 / α))
      = -(1 / 2) :=
  theta_logDeriv_dual hα

example : thetaDeriv Real.pi = -(theta Real.pi / (4 * Real.pi)) :=
  thetaDeriv_pi

example {α : ℝ} (hα : Real.pi ≤ α) :
    0 < α * thetaDeriv2 α + thetaDeriv α * theta α
      - α * thetaDeriv α ^ 2 :=
  theta_fluctuation_large hα

example {α : ℝ} (hα : Real.pi ≤ α) :
    0 < α * (thetaDeriv2 α * theta α - thetaDeriv α ^ 2)
      + thetaDeriv α * theta α :=
  theta_logDeriv_numer_pos_large hα

example : StrictMonoOn (fun α : ℝ => α * (thetaDeriv α / theta α))
    (Set.Ioi 0) :=
  theta_logDeriv_strictMonoOn

example {t a b : ℝ} (ht : 0 < t) (ha : 1 < a) (hb : 1 < b) :
    theta (a ^ 2 * t) * theta (b ^ 2 * t)
      < theta t * theta ((a * b) ^ 2 * t) :=
  theta_rect_strict ht ha hb

example {t a : ℝ} (ht : 0 < t) (ha : 1 < a) :
    theta (a ^ 2 * t) ^ 2 < theta t * theta (a ^ 4 * t) :=
  theta_sq_lt ht ha

/-! ## Diagonal forms -/

example {r : ℕ} {c : Fin r → ℝ} {s : ℝ} (hc : ∀ i, 0 < c i)
    (hs : 0 < s) {q q' : ℕ} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    diagDefect c s q q' = ∑ i, defect (c i * s) q q' :=
  diagDefect_eq_sum hc hs hq hq'

example {r : ℕ} {c : Fin r → ℝ} (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    {t a b : ℝ} (ht : 0 < t) (ha : 1 < a) (hb : 1 < b) :
    diagTheta c (a ^ 2 * t) * diagTheta c (b ^ 2 * t)
      < diagTheta c t * diagTheta c ((a * b) ^ 2 * t) :=
  diagTheta_rect_strict hr hc ht ha hb

example {r : ℕ} {c : Fin r → ℝ} (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    {t a : ℝ} (ht : 0 < t) (ha : 1 < a) :
    diagTheta c (a ^ 2 * t) ^ 2
      < diagTheta c t * diagTheta c (a ^ 4 * t) :=
  diagTheta_sq_lt hr hc ht ha

end Theaetetus
