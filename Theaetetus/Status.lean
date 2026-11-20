import Theaetetus.Duality
import Theaetetus.CosetSeparation
import Theaetetus.CosetDuality
import Theaetetus.CosetSign
import Theaetetus.SiegelDegree
import Theaetetus.FrameSeparation
import Theaetetus.Midpoint
import Theaetetus.Factorization
import Theaetetus.RankFunction
import Theaetetus.Classification
import Theaetetus.Peeling
import Theaetetus.LargeScale
import Theaetetus.SmallScale
import Theaetetus.StarObstruction
import Theaetetus.DiagonalCurvature
import Theaetetus.Certification
import Theaetetus.Tails
import Theaetetus.Shells
import Theaetetus.GramDuality
import Theaetetus.LatticeDuality
import Theaetetus.GramCurvature
import Theaetetus.Correlation
import Theaetetus.CorrelationEquality
import Theaetetus.ReflectionFourier
import Theaetetus.MassMaximum
import Theaetetus.ParitySeparation
import Theaetetus.EvenPartSeparation
import Theaetetus.LogMassFourier
import Theaetetus.ClusterExpansion
import Theaetetus.ClusterCoefficient
import Theaetetus.ResolutionMetric
import Theaetetus.DefinitenessBridge
import Theaetetus.GramAsymptotics
import Theaetetus.FiniteIndex
import Theaetetus.SublatticeAsymptotics
import Theaetetus.OrthogonalSum
import Theaetetus.HigherInteraction
import Theaetetus.SublatticeDiamond
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
fluctuation, and the strict rectangle; diagonal forms; certified
coercivity; certified tails; certified shell counts; higher-rank
defect duality; higher-rank thermodynamic curvature and its
duality; the field defect and the intrinsic lift; the
shifted mass and positive correlation; the orthogonal sum;
the arithmetic realization of the abstract defect and the
coprime telescope of its corrected orders; the Gaussian diamond of
sublattices; the equality cases of the correlation inequalities and
the Fourier form of the two-grid criterion; the strict maximum of
the shifted Gaussian mass, the separation of the parity feature
vectors, its real Gaussian core, the torus Fourier coefficients of
the logarithmic mass, its cluster normalization, and that expansion
read on coefficients; the resolution metric; the scale
asymptotics of a Gram Boltzmann sum, the finite-index mass ratio,
and the pairwise boundary of the sublattice field. -/

namespace Theaetetus

open Filter Topology Matrix UnitAddTorus

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

noncomputable example (T : PartitionTower) : PartitionTower :=
  T.residual

example (T : PartitionTower) {β : ℝ} (hβ : 1 ≤ β) :
    T.residual.Z β
      = T.Z β
        - (T.leastEnergyMult : ℝ)
          * Real.exp (-(β * T.leastEnergy)) :=
  T.residual_Z hβ

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal)
    (hres : ∃ k : T.residual.Λ, k ≠ T.residual.modal) :
    T.leastEnergy < T.residual.leastEnergy :=
  T.leastEnergy_lt_residual hnt hres

example (T : PartitionTower) (n : ℕ) {β : ℝ} (hβ : 1 ≤ β) :
    (T.peel n).Z β
      = T.Z β - ∑ i ∈ Finset.range n,
          ((T.peel i).leastEnergyMult : ℝ)
            * Real.exp (-(β * (T.peel i).leastEnergy)) :=
  T.peel_Z n hβ

example (T : PartitionTower) (n : ℕ)
    (hnt : ∃ k : (T.peel n).Λ, k ≠ (T.peel n).modal) :
    Tendsto (fun β : ℝ =>
        -Real.log ((T.Z β - ∑ i ∈ Finset.range n,
            ((T.peel i).leastEnergyMult : ℝ)
              * Real.exp (-(β * (T.peel i).leastEnergy))) - 1) / β)
      atTop (𝓝 (T.peel n).leastEnergy) :=
  T.tendsto_peel_leastEnergy n hnt

example (T : PartitionTower) (n : ℕ)
    (hnt : ∃ k : (T.peel n).Λ, k ≠ (T.peel n).modal) :
    Tendsto (fun β : ℝ =>
        Real.exp (β * (T.peel n).leastEnergy)
          * ((T.Z β - ∑ i ∈ Finset.range n,
              ((T.peel i).leastEnergyMult : ℝ)
                * Real.exp (-(β * (T.peel i).leastEnergy))) - 1))
      atTop (𝓝 ((T.peel n).leastEnergyMult : ℝ)) :=
  T.tendsto_peel_leastEnergyMult n hnt

example (T : PartitionTower) (n : ℕ)
    (hn : ∃ k : (T.peel n).Λ, k ≠ (T.peel n).modal)
    (hn1 : ∃ k : (T.peel (n + 1)).Λ, k ≠ (T.peel (n + 1)).modal) :
    (T.peel n).leastEnergy < (T.peel (n + 1)).leastEnergy :=
  T.peel_leastEnergy_strictMono n hn hn1

example (T : PartitionTower) (n : ℕ)
    (hnt : ∃ k : (T.peel n).Λ, k ≠ (T.peel n).modal) :
    Tendsto (fun m : ℕ =>
        -Real.log ((T.Z ((m : ℝ) ^ 2) - ∑ i ∈ Finset.range n,
            ((T.peel i).leastEnergyMult : ℝ)
              * Real.exp (-((m : ℝ) ^ 2 * (T.peel i).leastEnergy)))
          - 1) / (m : ℝ) ^ 2)
      atTop (𝓝 (T.peel n).leastEnergy) :=
  T.tendsto_peel_leastEnergy_sample n hnt

example (T : PartitionTower) (n : ℕ)
    (hnt : ∃ k : (T.peel n).Λ, k ≠ (T.peel n).modal) :
    Tendsto (fun m : ℕ =>
        Real.exp ((m : ℝ) ^ 2 * (T.peel n).leastEnergy)
          * ((T.Z ((m : ℝ) ^ 2) - ∑ i ∈ Finset.range n,
              ((T.peel i).leastEnergyMult : ℝ)
                * Real.exp (-((m : ℝ) ^ 2 * (T.peel i).leastEnergy)))
            - 1))
      atTop (𝓝 ((T.peel n).leastEnergyMult : ℝ)) :=
  T.tendsto_peel_leastEnergyMult_sample n hnt

example (T : PartitionTower) {β : ℝ} (hβ : 1 ≤ β) :
    T.Z β - 1
      = ∑' k : {k : T.Λ // k ≠ T.modal}, Real.exp (-(β * T.E k.1)) :=
  T.Z_sub_one hβ

example (T : PartitionTower) (n : ℕ) :
    Function.Injective (T.peelEmbed n) :=
  T.peelEmbed_injective n

example (T : PartitionTower) (n : ℕ) (k : (T.peel n).Λ) :
    T.E (T.peelEmbed n k) = (T.peel n).E k :=
  T.E_peelEmbed n k

example (T : PartitionTower) (n : ℕ) :
    T.peelEmbed n (T.peel n).modal = T.modal :=
  T.peelEmbed_modal n

example (T : PartitionTower) (n : ℕ) {k : (T.peel n).Λ}
    (hk : k ≠ (T.peel n).modal) : T.peelEmbed n k ≠ T.modal :=
  T.peelEmbed_ne_modal n hk

example (T : PartitionTower) :
    Antitone fun n : ℕ => Set.range (T.peelEmbed n) :=
  T.range_peelEmbed_antitone

example (T : PartitionTower) {j : T.Λ} (hj : j ≠ T.modal) :
    ∃ n : ℕ, j ∉ Set.range (T.peelEmbed n) :=
  T.exists_notMem_range_peelEmbed hj

example (T : PartitionTower) :
    (⋂ n : ℕ, Set.range (T.peelEmbed n)) = {T.modal} :=
  T.iInter_range_peelEmbed

example (T : PartitionTower) {β : ℝ} (hβ : 1 ≤ β) :
    Tendsto (fun n : ℕ => (T.peel n).Z β) atTop (𝓝 1) :=
  T.tendsto_peel_Z hβ

example (T : PartitionTower) {β : ℝ} (hβ : 1 ≤ β) :
    HasSum (fun n : ℕ => ((T.peel n).leastEnergyMult : ℝ)
        * Real.exp (-(β * (T.peel n).leastEnergy)))
      (T.Z β - 1) :=
  T.hasSum_peel_layers hβ

example (T : PartitionTower) {β : ℝ} (hβ : 1 ≤ β) :
    (∑' n : ℕ, ((T.peel n).leastEnergyMult : ℝ)
        * Real.exp (-(β * (T.peel n).leastEnergy)))
      = T.Z β - 1 :=
  T.tsum_peel_layers hβ

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

/-! ## Certified coercivity -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {μ : ℝ} (hμ : ∀ i, μ ≤ hM.eigenvalues i) (x : Fin d → ℝ) :
    μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x :=
  hM.mul_sum_sq_le_quadForm hμ x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {μ : ℝ} (h : ∀ x : Fin d → ℝ, μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x)
    (i : Fin d) :
    μ ≤ hM.eigenvalues i :=
  hM.le_eigenvalues_of_mul_sum_sq_le h i

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {μ : ℝ} :
    (∀ x : Fin d → ℝ, μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x)
      ↔ ∀ i, μ ≤ hM.eigenvalues i :=
  hM.mul_sum_sq_le_quadForm_iff

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hsym : M.IsSymm)
    {μ : ℝ}
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i)
    (x : Fin d → ℝ) :
    μ * ∑ i, x i ^ 2 ≤ x ⬝ᵥ M.mulVec x :=
  mul_sum_sq_le_quadForm_of_dominant hsym hdom x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hsym : M.IsSymm)
    {μ : ℝ} (hμ : 0 < μ)
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i) :
    M.PosDef :=
  posDef_of_dominant hsym hμ hdom

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {μ : ℝ}
    (hdom : ∀ i, μ + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ M i i)
    (i : Fin d) :
    μ ≤ hM.eigenvalues i :=
  le_eigenvalues_of_dominant hM hdom i

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ}
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (k : Fin r → ℤ) :
    μ * ∑ i, (k i : ℝ) ^ 2 ≤ A.energy k :=
  A.mul_sum_sq_le_energy hμ k

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {ν : ℝ} (hν : ∀ i, hM.eigenvalues i ≤ ν) (x : Fin d → ℝ) :
    x ⬝ᵥ M.mulVec x ≤ ν * ∑ i, x i ^ 2 :=
  hM.quadForm_le_mul_sum_sq hν x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {ν : ℝ}
    (h : ∀ x : Fin d → ℝ, x ⬝ᵥ M.mulVec x ≤ ν * ∑ i, x i ^ 2)
    (i : Fin d) :
    hM.eigenvalues i ≤ ν :=
  hM.eigenvalues_le_of_quadForm_le h i

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {ν : ℝ} :
    (∀ x : Fin d → ℝ, x ⬝ᵥ M.mulVec x ≤ ν * ∑ i, x i ^ 2)
      ↔ ∀ i, hM.eigenvalues i ≤ ν :=
  hM.quadForm_le_mul_sum_sq_iff

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hsym : M.IsSymm)
    {ν : ℝ}
    (hdom : ∀ i, M i i + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ ν)
    (x : Fin d → ℝ) :
    x ⬝ᵥ M.mulVec x ≤ ν * ∑ i, x i ^ 2 :=
  quadForm_le_mul_sum_sq_of_dominant hsym hdom x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {ν : ℝ}
    (hdom : ∀ i, M i i + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ ν)
    (i : Fin d) :
    hM.eigenvalues i ≤ ν :=
  eigenvalues_le_of_dominant hM hdom i

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {c : ℝ} {x : Fin d → ℝ}
    (hx : x ⬝ᵥ M.mulVec x < c * ∑ i, x i ^ 2) :
    ∃ i, hM.eigenvalues i < c :=
  hM.exists_eigenvalues_lt hx

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsHermitian)
    {c : ℝ} {x : Fin d → ℝ}
    (hx : c * ∑ i, x i ^ 2 < x ⬝ᵥ M.mulVec x) :
    ∃ i, c < hM.eigenvalues i :=
  hM.exists_lt_eigenvalues hx

/-! ## Certified tails -/

example (r : ℕ) (f : Fin r → ℤ → ℝ) (hf_nn : ∀ i z, 0 ≤ f i z)
    (hf_sum : ∀ i, Summable (f i)) :
    ∑' k : Fin r → ℤ, ∏ i, f i (k i) = ∏ i, ∑' z : ℤ, f i z :=
  QuadraticAction.tsum_finPi_prod r f hf_nn hf_sum

example {α : ℝ} (hα : 0 < α) (N : ℕ) :
    (∑' m : ℤ, if (N : ℤ) < |m| then Real.exp (-α * (m : ℝ) ^ 2) else 0)
      ≤ 2 * (Real.exp (-α * ((N : ℝ) + 1) ^ 2)
          * (1 - Real.exp (-(2 * α * ((N : ℝ) + 1))))⁻¹) :=
  theta_tail_le hα N

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-A.energy k.1))
      ≤ (r : ℝ) * theta μ ^ (r - 1)
          * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) :=
  A.tail_le hμ0 hμ N

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    A.toSectorAction.partFn
      ≤ (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
        + (r : ℝ) * theta μ ^ (r - 1)
            * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
                * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹)) :=
  A.partFn_le_box_add_tail hμ0 hμ N

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (N : ℕ) :
    A.toSectorAction.partFn ∈ Set.Icc
      (∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-A.energy k.1))
      ((∑' k : {k : Fin r → ℤ // ∀ i, |k i| ≤ (N : ℤ)},
          Real.exp (-A.energy k.1))
        + (r : ℝ) * theta μ ^ (r - 1)
            * (2 * (Real.exp (-μ * ((N : ℝ) + 1) ^ 2)
                * (1 - Real.exp (-(2 * μ * ((N : ℝ) + 1))))⁻¹))) :=
  A.partFn_mem_box_Icc hμ0 hμ N

example {r : ℕ} {E : (Fin r → ℤ) → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hcoer : ∀ k : Fin r → ℤ, ν * ∑ i, (k i : ℝ) ^ 2 ≤ E k)
    (N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        Real.exp (-E k.1))
      ≤ (r : ℝ) * theta ν ^ (r - 1)
          * (2 * (Real.exp (-ν * ((N : ℝ) + 1) ^ 2)
              * (1 - Real.exp (-(2 * ν * ((N : ℝ) + 1))))⁻¹)) :=
  tail_exp_le hν hcoer N

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) (m N : ℕ) :
    (∑' k : {k : Fin r → ℤ // ¬ ∀ i, |k i| ≤ (N : ℤ)},
        A.energy k.1 ^ m * Real.exp (-A.energy k.1))
      ≤ 2 ^ m * (m.factorial : ℝ)
          * ((r : ℝ) * theta (μ / 2) ^ (r - 1)
              * (2 * (Real.exp (-(μ / 2) * ((N : ℝ) + 1) ^ 2)
                  * (1 - Real.exp (-(2 * (μ / 2) * ((N : ℝ) + 1))))⁻¹))) :=
  A.moment_tail_le hμ0 hμ m N

/-! ## Certified shell counts -/

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) {k : Fin r → ℤ}
    (hk : A.energy k ≤ R) (i : Fin r) :
    |k i| ≤ (N : ℤ) :=
  A.abs_le_of_energy_le hμ0 hμ hRN hk i

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k ≤ R}.Finite :=
  A.finite_energy_sublevel hμ0 hμ hRN

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k ≤ R}.ncard ≤ (2 * N + 1) ^ r :=
  A.energy_sublevel_ncard_le hμ0 hμ hRN

example {r : ℕ} (A : QuadraticAction r) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : ∀ i, μ ≤ A.Q_posDef.1.eigenvalues i) {R : ℝ} {N : ℕ}
    (hRN : R < μ * ((N : ℝ) + 1) ^ 2) :
    {k : Fin r → ℤ | A.energy k = R}.ncard ≤ (2 * N + 1) ^ r :=
  A.energy_shell_ncard_le hμ0 hμ hRN

/-! ## Higher-rank defect duality -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) :
    gramTheta M⁻¹ (Real.pi ^ 2 / α)
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2)
          * gramTheta M α :=
  gramTheta_dual hM hα

example (α : ℝ) :
    gramTheta (!![1] : Matrix (Fin 1) (Fin 1) ℝ) α = theta α :=
  gramTheta_one_eq_theta α

example (s : ℝ) (q q' : ℕ) :
    gramDefect (!![1] : Matrix (Fin 1) (Fin 1) ℝ) s q q'
      = defect s q q' :=
  gramDefect_one_eq_defect s q q'

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    gramDefect M s q q'
      = gramDefect M⁻¹
          (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  gramDefect_dual hM hs hq hq'

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hco : Nat.Coprime p q) :
    gramDefect M s p q
      = gramDefect M⁻¹
          (Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s)) p q :=
  gramDefect_dual_coprime hM hs hp hq hco

/-! ## The field defect and the intrinsic lift -/

example {Z Z' : ℝ → ℝ} {a b : ℝ}
    (hrefl : ∀ α : ℝ, 0 < α →
      Real.log (Z' (Real.pi ^ 2 / α))
        = a * Real.log α + b + Real.log (Z α))
    {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect Z s q q'
      = fieldDefect Z' (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  fieldDefect_dual_of_log_reflect hrefl hs hq hq'

example (s : ℝ) (q q' : ℕ) :
    defect s q q' = fieldDefect theta s q q' :=
  defect_eq_fieldDefect s q q'

example (Z : ℝ → ℝ) (s : ℝ) (q q' : ℕ) :
    fieldDefect Z s q q' = fieldDefect Z s q' q :=
  fieldDefect_comm Z s q q'

example (Z : ℝ → ℝ) (s : ℝ) {q q' : ℕ} (hdvd : q ∣ q') :
    fieldDefect Z s q q' = 0 :=
  fieldDefect_eq_zero_of_dvd Z s hdvd

example (Z : ℝ → ℝ) (s : ℝ) (q : ℕ) :
    fieldDefect Z s q q = 0 :=
  fieldDefect_self Z s q

example (T : PartitionTower) (q q' : ℕ) :
    T.defect q q' = fieldDefect T.Z 1 q q' :=
  T.defect_eq_fieldDefect q q'

example (T : PartitionTower) (q q' : ℕ) :
    T.defect q q' = T.defect q' q :=
  T.defect_comm q q'

example (T : PartitionTower) (q : ℕ) : T.defect q q = 0 :=
  T.defect_self q

example {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (q q' : ℕ) :
    gramDefect M s q q' = fieldDefect (gramTheta M) s q q' :=
  gramDefect_eq_fieldDefect M s q q'

example (Q : QuadLatticeAction) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ) (β : ℝ) :
    Q.scaledPartFn β = gramTheta (Q.gram b) β :=
  Q.scaledPartFn_eq_gramTheta b β

example (Q : QuadLatticeAction) {n m : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ)
    (b' : Module.Basis (Fin m) ℤ Q.Λ) (s : ℝ) (q q' : ℕ) :
    gramDefect (Q.gram b) s q q' = gramDefect (Q.gram b') s q q' :=
  Q.gramDefect_gram_eq b b' s q q'

example (Q : QuadLatticeAction) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ) (s : ℝ) (q q' : ℕ) :
    Q.defect s q q' = gramDefect (Q.gram b) s q q' :=
  Q.defect_eq_gramDefect b s q q'

example (Q : QuadLatticeAction) (q q' : ℕ) :
    Q.toPartitionTower.defect q q' = Q.defect 1 q q' :=
  Q.toPartitionTower_defect q q'

example (Q : QuadLatticeAction) :
    Q.dual.gram (Module.finBasis ℤ Q.Λ).dualBasis
      = (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ :=
  Q.dual_gram

example (Q : QuadLatticeAction) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.dual.gram b.dualBasis = (Q.gram b)⁻¹ :=
  Q.dual_gram_at b

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    Q.defect s q q'
      = Q.dual.defect (Real.pi ^ 2 / ((Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  Q.defect_dual hs hq hq'

/-! ## Higher-rank thermodynamic curvature -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (m : ℕ)
    {α : ℝ} (hα : 0 < α) :
    HasDerivAt (gramMoment M m) (-gramMoment M (m + 1) α) α :=
  hasDerivAt_gramMoment hM m hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) :
    HasDerivAt (fun β => Real.log (gramTheta M β)) (-gramMeanEnergy M α) α :=
  hasDerivAt_log_gramTheta hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) :
    HasDerivAt (gramMeanEnergy M) (-gramVariance M α) α :=
  hasDerivAt_gramMeanEnergy hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (hd : 0 < d) :
    StrictAntiOn (gramMeanEnergy M) (Set.Ioi 0) :=
  gramMeanEnergy_strictAntiOn hM hd

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) :
    α * gramMeanEnergy M α + Real.pi ^ 2 / α * gramMeanEnergy M⁻¹ (Real.pi ^ 2 / α)
      = (d : ℝ) / 2 :=
  gramMeanEnergy_dual hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) :
    gramCurvature M α = gramCurvature M⁻¹ (Real.pi ^ 2 / α) :=
  gramCurvature_dual hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {β : ℝ} (hβ : 0 < β) :
    logCurvature (gramTheta M) β = β ^ 2 * gramVariance M β - β * gramMeanEnergy M β :=
  logCurvature_gramTheta hM hβ

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    (h : ∀ β, Real.pi ≤ β → β * gramMeanEnergy M β < β ^ 2 * gramVariance M β)
    (h' : ∀ β, Real.pi ≤ β → β * gramMeanEnergy M⁻¹ β < β ^ 2 * gramVariance M⁻¹ β)
    {β : ℝ} (hβ : 0 < β) : β * gramMeanEnergy M β < β ^ 2 * gramVariance M β :=
  gramCurvature_pos_of_ge_pi hM h h' hβ

example (Q : QuadLatticeAction) {β : ℝ} (hβ : 0 < β) :
    logCurvature Q.scaledPartFn β = logCurvature Q.dual.scaledPartFn (Real.pi ^ 2 / β) :=
  Q.logCurvature_dual hβ

example (Q : QuadLatticeAction)
    (h : ∀ β, Real.pi ≤ β → 0 < logCurvature Q.scaledPartFn β)
    (h' : ∀ β, Real.pi ≤ β → 0 < logCurvature Q.dual.scaledPartFn β)
    {β : ℝ} (hβ : 0 < β) : 0 < logCurvature Q.scaledPartFn β :=
  Q.logCurvature_pos_of_ge_pi h h' hβ

/-! ## The shifted mass and positive correlation -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M α x
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α)
            ((n : ℝ)⁻¹ • (x + fun i => ((c i).val : ℝ))) :=
  gramMass_coset hM hα x n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      = ∑ c : Fin d → ZMod 2,
          gramMass M (2 * α)
            ((2 : ℝ)⁻¹ • (x + y + fun i => ((c i).val : ℝ)))
          * gramMass M (2 * α)
            ((2 : ℝ)⁻¹ • (x - y + fun i => ((c i).val : ℝ))) :=
  gramMass_mul_gramMass hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (z : Fin d → ℝ) (c : Fin d → ZMod 2) :
    0 < parityVector M α z c :=
  parityVector_pos hM hα z c

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      = ∑ c : Fin d → ZMod 2,
          parityVector M α (x + y) c * parityVector M α (x - y) c :=
  gramMass_mul_eq_inner hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (z : Fin d → ℝ) :
    ∑ c : Fin d → ZMod 2, parityVector M α z c ^ 2
      = gramMass M α 0 * gramMass M α z :=
  sum_sq_parityVector hM hα z

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x ^ 2 * gramMass M α y ^ 2
      ≤ gramMass M α 0 ^ 2
          * (gramMass M α (x + y) * gramMass M α (x - y)) :=
  gramMass_sq_mul_sq_le hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
      ≤ gramMass M α 0
          * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2) :=
  gramMass_mul_le_avg hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
      ≤ gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x :=
  gramMass_dilate_mul_le hM hα x n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x)
            * gramMass M ((n : ℝ) ^ 2 * α) (residueShift n c) :=
  gramMass_dilate_mul_eq_sum hM hα x n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x
      = ∑ c : Fin d → ZMod n,
          gramMass M ((n : ℝ) ^ 2 * α) 0
            * ((gramMass M ((n : ℝ) ^ 2 * α)
                  (dilateShift n x + residueShift n c)
                + gramMass M ((n : ℝ) ^ 2 * α)
                  (dilateShift n x - residueShift n c)) / 2) :=
  gramMass_dilate_avg_eq_sum hM hα x n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
      ≤ gramMass M s 0
          * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0 :=
  gramMass_coprime_mul_le hM hs ha hb hco

example {d : ℕ} (a b : ℕ) (r : Fin d → ZMod b) :
    dilatedResidueShift a b r = (a : ℝ) • residueShift b r :=
  dilatedResidueShift_eq a b r

example {d : ℕ} {a : ℕ} (ha : 0 < a) (b : ℕ) (r : Fin d → ZMod b) :
    dilateShift a (dilatedResidueShift a b r) = residueShift b r :=
  dilateShift_dilatedResidueShift ha b r

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} [NeZero b] (hco : Nat.Coprime a b) :
    ∑ r : Fin d → ZMod b,
        gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r)
      = gramMass M s 0 :=
  sum_gramMass_dilatedResidueShift hM hs hco

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) [NeZero b] :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
      = ∑ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
              (dilateShift a (dilatedResidueShift a b r))
            * gramMass M ((b : ℝ) ^ 2 * s) 0 :=
  gramMass_coprime_mul_eq_sum hM hs ha

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} [NeZero b] (hco : Nat.Coprime a b) :
    gramMass M s 0 * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      = ∑ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
            * gramMass M ((b : ℝ) ^ 2 * s) (dilatedResidueShift a b r) :=
  gramMass_coprime_avg_eq_sum hM hs hco

example (Z : ℝ → ℝ) (s : ℝ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect Z s q q'
      = fieldDefect Z ((Nat.gcd q q' : ℝ) ^ 2 * s)
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  fieldDefect_div_gcd Z s hq hq'

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    gramDefect M s q q' ≤ 0 :=
  gramDefect_nonpos hM hs hq hq'

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    Q.defect s q q' ≤ 0 :=
  Q.defect_nonpos hs hq hq'

/-! ## The equality cases of the correlation inequalities -/

example {ι : Type} [Fintype ι] [Nonempty ι] {f g : ι → ℝ}
    (hf : ∀ i, 0 < f i) (hg : ∀ i, 0 < g i) :
    (∑ i, f i * g i) ^ 2 = (∑ i, f i ^ 2) * (∑ i, g i ^ 2)
      ↔ ∃ r : ℝ, 0 < r ∧ ∀ i, f i = r * g i :=
  sum_mul_sq_eq_sq_mul_sq_iff_of_pos hf hg

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x ^ 2 * gramMass M α y ^ 2
        = gramMass M α 0 ^ 2
            * (gramMass M α (x + y) * gramMass M α (x - y))
      ↔ ParityCollinear M α (x + y) (x - y) :=
  gramMass_sq_mul_sq_eq_iff hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
        = gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)
      ↔ ParityCollinear M α (x + y) (x - y)
          ∧ gramMass M α (x + y) = gramMass M α (x - y) :=
  gramMass_mul_eq_avg_iff hM hα x y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x y : Fin d → ℝ) :
    gramMass M α x * gramMass M α y
        = gramMass M α 0
            * ((gramMass M α (x + y) + gramMass M α (x - y)) / 2)
      ↔ parityVector M α (x + y) = parityVector M α (x - y) :=
  gramMass_mul_eq_avg_iff_parityVector_eq hM hα x y

example {ι : Type} [Fintype ι] {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    (∑ i, f i) = ∑ i, g i ↔ ∀ i, f i = g i :=
  sum_eq_iff_of_le h

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {α : ℝ} (hα : 0 < α) (x : Fin d → ℝ) (n : ℕ) [NeZero n] :
    gramMass M ((n : ℝ) ^ 2 * α) (dilateShift n x) * gramMass M α 0
        = gramMass M ((n : ℝ) ^ 2 * α) 0 * gramMass M α x
      ↔ ∀ c : Fin d → ZMod n,
          parityVector M ((n : ℝ) ^ 2 * α)
              (dilateShift n x + residueShift n c)
            = parityVector M ((n : ℝ) ^ 2 * α)
                (dilateShift n x - residueShift n c) :=
  gramMass_dilate_mul_eq_iff hM hα x n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
        = gramMass M s 0
            * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      ↔ ∀ r : Fin d → ZMod b,
          gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
                (dilateShift a (dilatedResidueShift a b r))
              * gramMass M ((b : ℝ) ^ 2 * s) 0
            = gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
                * gramMass M ((b : ℝ) ^ 2 * s)
                    (dilatedResidueShift a b r) :=
  gramMass_coprime_mul_eq_iff_forall_class hM hs ha hb hco

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
        = gramMass M s 0
            * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0
      ↔ ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a),
          parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
              (residueShift b r + residueShift a c)
            = parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
                (residueShift b r - residueShift a c) :=
  gramMass_coprime_mul_eq_iff hM hs ha hb hco

example {Z : ℝ → ℝ} (hZ : ∀ β, 0 < β → 0 < Z β) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    fieldDefect Z s a b = 0
      ↔ Z ((a : ℝ) ^ 2 * s) * Z ((b : ℝ) ^ 2 * s)
          = Z s * Z (((a * b : ℕ) : ℝ) ^ 2 * s) :=
  fieldDefect_eq_zero_iff_mul_eq hZ hs ha hb hco

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramDefect M s a b = 0
      ↔ gramMass M ((a : ℝ) ^ 2 * s) 0 * gramMass M ((b : ℝ) ^ 2 * s) 0
          = gramMass M s 0
              * gramMass M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) 0 :=
  gramDefect_eq_zero_iff_mul_eq hM hs ha hb hco

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    gramDefect M s a b = 0 ↔ TwoGridReflection M s a b :=
  gramDefect_eq_zero_iff_twoGridReflection hM hs ha hb hco

example (Q : QuadLatticeAction) {n : ℕ}
    (bs : Module.Basis (Fin n) ℤ Q.Λ) {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    Q.defect s a b = 0 ↔ TwoGridReflection (Q.gram bs) s a b :=
  Q.defect_eq_zero_iff_twoGridReflection bs hs ha hb hco

example (Q : QuadLatticeAction) {n m : ℕ}
    (bs : Module.Basis (Fin n) ℤ Q.Λ) (bs' : Module.Basis (Fin m) ℤ Q.Λ)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    TwoGridReflection (Q.gram bs) s a b
      ↔ TwoGridReflection (Q.gram bs') s a b :=
  Q.twoGridReflection_gram_iff bs bs' hs ha hb hco

/-! ## The Fourier form of the two-grid criterion -/

example {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) (x : Fin d → ℝ) :
    gramMass M α x = periodization ((α / Real.pi) • M) x :=
  gramMass_eq_periodization M α x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (m : Fin d → ℤ) : 0 < massFourierCoeff M α m :=
  massFourierCoeff_pos hM hα m

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        massFourierCoeff M α m
          * Real.cos (2 * Real.pi * dualPairing m x))
      (gramMass M α x) :=
  hasSum_massFourier_cos hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (y t : Fin d → ℝ) :
    gramMass M α (y + t) = gramMass M α (y - t)
      ↔ (∑' m : Fin d → ℤ, massFourierCoeff M α m
            * (Real.sin (2 * Real.pi * dualPairing m y)
                * Real.sin (2 * Real.pi * dualPairing m t))) = 0 :=
  gramMass_reflect_iff hM hα y t

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    TwoGridReflection M s a b
      ↔ ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a) (e : Fin d → ZMod 2),
          (∑' m : Fin d → ℤ,
              massFourierCoeff M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) m
                * (Real.sin (2 * Real.pi
                      * dualPairing m (anchorShift b r e))
                    * Real.sin (2 * Real.pi
                      * dualPairing m (displaceShift a c)))) = 0 :=
  twoGridReflection_iff_fourier hM hs ha hb

example {d : ℕ} (b : ℕ) [NeZero b] (r : Fin d → ZMod b)
    (e : Fin d → ZMod 2) :
    anchorShift b r e
      = residueShift (2 * b)
          (fun i => (((r i).val + b * (e i).val : ℕ) : ZMod (2 * b))) :=
  anchorShift_eq_residueShift b r e

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        ((massFourierCoeff M α m : ℝ) : ℂ)
          * UnitAddTorus.mFourier m (torusMk x))
      ((gramMass M α x : ℝ) : ℂ) :=
  hasSum_massFourier hM hα x

example {d : ℕ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) {r r' : Fin d → ZMod b}
    {e e' : Fin d → ZMod 2} {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    ∃ z : Fin d → ℤ,
      (2 : ℝ) • (displaceShift a c + displaceShift a c')
        = fun i => ((z i : ℤ) : ℝ) :=
  chain_displacement_int ha hb hco h

example {d : ℕ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) {r r' : Fin d → ZMod b}
    {e e' : Fin d → ZMod 2} {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    ∃ z : Fin d → ℤ,
      anchorShift b r e + displaceShift a c
        = (anchorShift b r' e' - displaceShift a c')
            + fun i => ((z i : ℤ) : ℝ) :=
  chain_endpoints_int ha hb hco h

example {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b)
    {r r' : Fin d → ZMod b} {e e' : Fin d → ZMod 2}
    {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    gramMass M α (anchorShift b r e + displaceShift a c)
      = gramMass M α (anchorShift b r' e' - displaceShift a c') :=
  gramMass_chain_eq M α ha hb hco h

/-! ## The CRT grid and the alias classes -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    TwoGridReflection M s a b ↔ TwoGridReflection M s b a :=
  twoGridReflection_comm hM hs ha hb hco

example {a b : ℕ} (hco : Nat.Coprime (2 * b) a) :
    ∃ U : ℤ, (2 * (b : ℤ)) ∣ U - 1 ∧ (a : ℤ) ∣ U + 1 :=
  exists_crtInvolution hco

example {a b : ℕ} (hodd : ¬ 2 ∣ a) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) (k c : ℤ) :
    ((2 * b * a : ℕ) : ℤ)
      ∣ U * ((a : ℤ) * k + (b : ℤ) * c) - ((a : ℤ) * k - (b : ℤ) * c) :=
  crtInvolution_dvd hodd h1 h2 k c

example {a b : ℕ} {U : ℤ} (h1 : (2 * (b : ℤ)) ∣ U - 1)
    (h2 : (a : ℤ) ∣ U + 1) :
    (2 * (b : ℤ) * (a : ℤ)) ∣ U ^ 2 - 1 :=
  crtInvolution_sq h1 h2

example {a b : ℕ} (hodd : ¬ 2 ∣ a) (ha : 1 < a) (hb : 1 < b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    ¬ ((2 * b * a : ℕ) : ℤ) ∣ U - 1 ∧ ¬ ((2 * b * a : ℕ) : ℤ) ∣ U + 1 :=
  crtInvolution_nontrivial hodd ha hb h1 h2

example {a b : ℕ} [NeZero a] [NeZero b]
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) :
    Function.Bijective
      (fun p : ZMod (2 * b) × ZMod a => jointIndex a b p.1 p.2) :=
  ⟨jointIndex_injective hco hab, jointIndex_surjective hco hab⟩

example {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) {a b : ℕ}
    [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a) (hco : Nat.Coprime (2 * b) a)
    (hab : Nat.Coprime a b) {U : ℤ} (h1 : (2 * (b : ℤ)) ∣ U - 1)
    (h2 : (a : ℤ) ∣ U + 1) :
    TwoGridReflection M s a b
      ↔ ∀ n : Fin d → ZMod (2 * b * a),
          gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
              (residueShift (2 * b * a) n)
            = gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
                (residueShift (2 * b * a)
                  (fun i => (U : ZMod (2 * b * a)) * n i)) :=
  twoGridReflection_iff_crt M s hodd hco hab h1 h2

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {L : ℕ} [NeZero L] (ν : Fin d → ZMod L) :
    0 < aliasSum M α L ν :=
  aliasSum_pos hM hα ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {L : ℕ} [NeZero L] (n : Fin d → ZMod L) :
    ((gramMass M α (residueShift L n) : ℝ) : ℂ)
      = ∑ ν : Fin d → ZMod L, ((aliasSum M α L ν : ℝ) : ℂ) * gridChar ν n :=
  gramMass_eq_sum_aliasSum hM hα n

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    TwoGridReflection M s a b
      ↔ ∀ ν : Fin d → ZMod (2 * b * a),
          aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
            = aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
                (fun i => (U : ZMod (2 * b * a)) * ν i) :=
  twoGridReflection_iff_alias hM hs hodd hco hab h1 h2

example {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) (hab : ¬ a ∣ b) (hba : ¬ b ∣ a) :
    ¬ TwoGridReflection (!![1] : Matrix (Fin 1) (Fin 1) ℝ) s a b :=
  not_twoGridReflection_rankOne hs ha hb hco hab hba

example {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hodd : ¬ 2 ∣ a) (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b)
    {U : ℤ} (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    ∃ ν : Fin 1 → ZMod (2 * b * a),
      aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
          (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
        ≠ aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
            (fun i => (U : ZMod (2 * b * a)) * ν i) :=
  exists_aliasSum_ne_rankOne hs ha hb hodd hco hab h1 h2

/-! ## The duality loop -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (m : Fin d → ℤ) :
    massFourierCoeff M α m
      = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
        * Real.exp (-(Real.pi ^ 2 / α)
            * ∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) :=
  massFourierCoeff_eq hM hα m

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {L : ℕ} [NeZero L] (ν : Fin d → ZMod L) :
    aliasSum M α L ν
      = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
        * gramMass M⁻¹ (Real.pi ^ 2 * (L : ℝ) ^ 2 / α)
            (residueShift L ν) :=
  aliasSum_eq_dual hM hα ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) :
    TwoGridReflection M s a b
      ↔ TwoGridReflection M⁻¹
          (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)) a b :=
  twoGridReflection_dual hM hs ha hb hco

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    (∀ ν : Fin d → ZMod (2 * b * a),
        aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
          = aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
              (fun i => (U : ZMod (2 * b * a)) * ν i))
      ↔ TwoGridReflection M⁻¹
          (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)) a b :=
  aliasSum_invariant_iff_dual hM hs hodd hco hab h1 h2

/-! ## The orthogonal sum -/

example {Z W : ℝ → ℝ} (h : ∀ β : ℝ, 0 < β → Z β = W β) {s : ℝ}
    (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect Z s q q' = fieldDefect W s q q' :=
  fieldDefect_congr h hs hq hq'

example {Z Z' : ℝ → ℝ} (hZ : ∀ β : ℝ, 0 < β → 0 < Z β)
    (hZ' : ∀ β : ℝ, 0 < β → 0 < Z' β) {s : ℝ} (hs : 0 < s)
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect (fun β => Z β * Z' β) s q q'
      = fieldDefect Z s q q' + fieldDefect Z' s q q' :=
  fieldDefect_mul hZ hZ' hs hq hq'

example (Q : QuadLatticeAction) {β : ℝ} (hβ : 0 < β) :
    0 < Q.scaledPartFn β :=
  Q.scaledPartFn_pos hβ

example (Q Q' : QuadLatticeAction) {β : ℝ} (hβ : 0 < β) :
    (Q.orthSum Q').scaledPartFn β
      = Q.scaledPartFn β * Q'.scaledPartFn β :=
  QuadLatticeAction.orthSum_scaledPartFn Q Q' hβ

example (Q Q' : QuadLatticeAction) {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    (Q.orthSum Q').defect s q q'
      = Q.defect s q q' + Q'.defect s q q' :=
  QuadLatticeAction.orthSum_defect Q Q' hs hq hq'

example (Q Q' : QuadLatticeAction) {s : ℝ} (hs : 0 < s) {q q' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') :
    (Q.orthSum Q').defect s q q' = 0
      ↔ Q.defect s q q' = 0 ∧ Q'.defect s q q' = 0 :=
  QuadLatticeAction.orthSum_defect_eq_zero_iff Q Q' hs hq hq'

example (Q Q' : QuadLatticeAction) {t a b : ℝ} (ht : 0 < t)
    (ha : 1 < a) (hb : 1 < b)
    (h : Q.scaledPartFn (a ^ 2 * t) * Q.scaledPartFn (b ^ 2 * t)
      < Q.scaledPartFn t * Q.scaledPartFn ((a * b) ^ 2 * t))
    (h' : Q'.scaledPartFn (a ^ 2 * t) * Q'.scaledPartFn (b ^ 2 * t)
      < Q'.scaledPartFn t * Q'.scaledPartFn ((a * b) ^ 2 * t)) :
    (Q.orthSum Q').scaledPartFn (a ^ 2 * t)
        * (Q.orthSum Q').scaledPartFn (b ^ 2 * t)
      < (Q.orthSum Q').scaledPartFn t
        * (Q.orthSum Q').scaledPartFn ((a * b) ^ 2 * t) :=
  QuadLatticeAction.orthSum_rect_strict Q Q' ht ha hb h h'

example (Q Q' : QuadLatticeAction) {t a b : ℝ} (ht : 0 < t)
    (ha : 1 < a) (hb : 1 < b)
    (hfail : ¬ ((Q.orthSum Q').scaledPartFn (a ^ 2 * t)
        * (Q.orthSum Q').scaledPartFn (b ^ 2 * t)
      < (Q.orthSum Q').scaledPartFn t
        * (Q.orthSum Q').scaledPartFn ((a * b) ^ 2 * t))) :
    ¬ (Q.scaledPartFn (a ^ 2 * t) * Q.scaledPartFn (b ^ 2 * t)
        < Q.scaledPartFn t * Q.scaledPartFn ((a * b) ^ 2 * t))
    ∨ ¬ (Q'.scaledPartFn (a ^ 2 * t) * Q'.scaledPartFn (b ^ 2 * t)
        < Q'.scaledPartFn t * Q'.scaledPartFn ((a * b) ^ 2 * t)) :=
  QuadLatticeAction.rect_strict_descend Q Q' ht ha hb hfail

/-! ## The arithmetic realization of the abstract defect -/

example (Z : ℝ → ℝ) (s : ℝ) (n m : ℕ+) :
    fieldDefect Z s (n : ℕ) (m : ℕ)
      = Descent.defect (logField Z s)
          (Descent.Arith.of n) (Descent.Arith.of m) :=
  fieldDefect_eq_defect Z s n m

example {a : ℕ+} {l : List ℕ+} (h : PairwiseCoprime (a :: l)) :
    Descent.supFam (Descent.Arith.of a) (l.map Descent.Arith.of)
      = Descent.Arith.of (prodFam a l) :=
  supFam_of_pairwiseCoprime h

example (K : Descent.ContextField Descent.Arith ℝ) (d a : ℕ+) (l : List ℕ+)
    (hd : ∀ x ∈ a :: l, Nat.Coprime (x : ℕ) (d : ℕ))
    (hl : PairwiseCoprime (a :: l)) :
    Descent.defectFam K (Descent.Arith.of d) ((a :: l).map Descent.Arith.of)
      = Descent.defectFam K (Descent.Arith.of a) (l.map Descent.Arith.of)
        + Descent.defect K (Descent.Arith.of (prodFam a l))
            (Descent.Arith.of d) :=
  defectFam_cons_coprime K d a l hd hl

example (Z : ℝ → ℝ) (s : ℝ) (d : ℕ+) (l : List ℕ+)
    (h : PairwiseCoprime (d :: l)) :
    telescope Z s d l
      = Descent.telescope (logField Z s) (Descent.Arith.of d)
          (l.map Descent.Arith.of) :=
  telescope_eq_descent_telescope Z s d l h

example (Z : ℝ → ℝ) (s : ℝ) (d : ℕ+) (l : List ℕ+)
    (h : PairwiseCoprime (d :: l)) :
    Descent.defectFam (logField Z s) (Descent.Arith.of d)
        (l.map Descent.Arith.of)
      = telescope Z s d l :=
  defectFam_logField_eq_telescope Z s d l h

example (Z : ℝ → ℝ) (s : ℝ) {d d' : ℕ+} {l l' : List ℕ+}
    (hp : (d :: l).Perm (d' :: l')) (h : PairwiseCoprime (d :: l)) :
    telescope Z s d l = telescope Z s d' l' :=
  telescope_eq_of_perm Z s hp h

example {s : ℝ} (hs : 0 < s) {d : ℕ+} {l : List ℕ+} (hne : l ≠ [])
    (h : PairwiseCoprime (d :: l)) (hnt : ∀ x ∈ d :: l, 1 < (x : ℕ)) :
    Descent.defectFam (logField theta s) (Descent.Arith.of d)
        (l.map Descent.Arith.of) < 0 :=
  defectFam_theta_neg hs hne h hnt

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s) (d : ℕ+) (l : List ℕ+)
    (h : PairwiseCoprime (d :: l)) :
    Descent.defectFam (logField Q.scaledPartFn s) (Descent.Arith.of d)
        (l.map Descent.Arith.of) ≤ 0 :=
  Q.defectFam_nonpos hs d l h

example (Z : ℝ → ℝ) (s : ℝ) (a b c : ℕ+) (h : PairwiseCoprime [a, b, c]) :
    Descent.mixedDiff
        [Descent.Arith.of a, Descent.Arith.of b, Descent.Arith.of c]
        (logField Z s) (Descent.Arith.of 1)
      = fieldDefect Z s ((a : ℕ+) : ℕ) ((c : ℕ+) : ℕ)
        + fieldDefect Z s ((b : ℕ+) : ℕ) ((c : ℕ+) : ℕ)
        - fieldDefect Z s ((a * b : ℕ+) : ℕ) ((c : ℕ+) : ℕ) :=
  mixedDiff_triple_of_pairwiseCoprime Z s a b c h

example (Z : ℝ → ℝ) (s : ℝ) :
    Descent.mixedDiff
        [Descent.Arith.of 2, Descent.Arith.of 3, Descent.Arith.of 5]
        (logField Z s) (Descent.Arith.of 1)
      = fieldDefect Z s 2 5 + fieldDefect Z s 3 5 - fieldDefect Z s 6 5 :=
  mixedDiff_two_three_five Z s

example {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (logField theta s) (Descent.Arith.of 2)
      (Descent.Arith.of 3) (Descent.Arith.of 5) < 0 :=
  defect3_theta_235_neg hs

/-! ## The Gaussian diamond of sublattices -/

example : LatticeHom Descent.Diamond (AddSubgroup (ℤ × ℤ)) :=
  diamondHom

example : Function.Injective diamondSub :=
  diamondSub_injective

example : evenFst ⊓ evenSum = evenBoth :=
  inf_evenFst_evenSum

example : evenFst ⊔ evenSum = ⊤ :=
  sup_evenFst_evenSum

example {s : ℝ} (hs : 0 < s) (H : AddSubgroup (ℤ × ℤ)) : 0 < latMass s H :=
  latMass_pos hs H

example {s : ℝ} (hs : 0 < s) : latMass s ⊤ = theta s ^ 2 :=
  latMass_top hs

example {s : ℝ} (hs : 0 < s) : latMass s evenBoth = theta (4 * s) ^ 2 :=
  latMass_evenBoth hs

example {s : ℝ} (hs : 0 < s) :
    latMass s evenSnd = theta s * theta (4 * s) :=
  latMass_evenSnd hs

example {s : ℝ} (hs : 0 < s) :
    latMass s evenFst = theta s * theta (4 * s) :=
  latMass_evenFst hs

example {s : ℝ} (hs : 0 < s) : latMass s evenSum = theta (2 * s) ^ 2 :=
  latMass_evenSum hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSnd = 0 :=
  defect_evenFst_evenSnd hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSum
      = 2 * Real.log (theta (2 * s)) - Real.log (theta s)
        - Real.log (theta (4 * s)) :=
  defect_evenFst_evenSum hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenFst evenSum
      = Descent.defect (latField s) evenSnd evenSum :=
  defect_evenFst_evenSum_eq_evenSnd hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect (latField s) evenSnd evenSum < 0 :=
  defect_evenSnd_evenSum_neg hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s ∘ diamondHom) Descent.Diamond.x
        Descent.Diamond.y Descent.Diamond.z
      = 2 * Real.log (theta (2 * s) / theta (4 * s)) :=
  defect3_diamondHom hs

example {s : ℝ} (hs : 0 < s) (p q : Descent.Diamond) :
    Descent.defect (latField s ∘ diamondHom) p q ≤ 0 :=
  defect_diamondHom_nonpos hs p q

example {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s) evenFst evenSnd evenSum
      = latField s evenSum - latField s evenBoth :=
  defect3_diamond hs

example {s : ℝ} (hs : 0 < s) :
    Descent.defect3 (latField s) evenFst evenSnd evenSum
      = 2 * Real.log (theta (2 * s) / theta (4 * s)) :=
  defect3_diamond_eq hs

example {s : ℝ} (hs : 0 < s) :
    0 < Descent.defect3 (latField s) evenFst evenSnd evenSum :=
  defect3_diamond_pos hs

example :
    Tendsto (fun s => Descent.defect3 (latField s) evenFst evenSnd evenSum)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)) :=
  tendsto_defect3_diamond

example : evenFst.index = 2 :=
  index_evenFst

example : evenSnd.index = 2 :=
  index_evenSnd

example : evenSum.index = 2 :=
  index_evenSum

example : evenBoth.relIndex evenSum = 2 :=
  relIndex_evenBoth_evenSum

example :
    Tendsto (fun s => Descent.defect3 (latField s) evenFst evenSnd evenSum)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((evenBoth.relIndex evenSum : ℕ) : ℝ))) :=
  tendsto_defect3_diamond_index

example {α β : ℝ} (hα : 0 < α) (hαβ : α < β) : theta β < theta α :=
  theta_lt_theta hα hαβ

example {s : ℝ} (hs : 0 < s) :
    Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)
      = (0,
        2 * Real.log (theta (2 * s)) - Real.log (theta s)
          - Real.log (theta (4 * s)),
        2 * Real.log (theta (2 * s)) - Real.log (theta s)
          - Real.log (theta (4 * s)),
        2 * Real.log (theta (2 * s) / theta (4 * s))) :=
  canonicalDatum_diamondHom hs

example {s : ℝ} (hs : 0 < s) :
    ¬ Descent.Diamond.CanonicalDatumRealizable
        (Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).1
        (Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).2.1
        (Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).2.2.1
        (Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).2.2.2
      ∧ ¬ Descent.Diamond.CanonicalDatumRealizable
        (-(Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).1)
        (-(Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).2.1)
        (-(Descent.Diamond.canonicalDatum (latField s ∘ diamondHom)).2.2.1)
        (-(Descent.Diamond.canonicalDatum
          (latField s ∘ diamondHom)).2.2.2) :=
  not_canonicalDatumRealizable_diamondHom hs

example {s : ℝ} (hs : 0 < s) :
    ¬ Descent.Realizable (latField s ∘ diamondHom) :=
  not_realizable_diamondHom hs

example {s : ℝ} (hs : 0 < s) :
    (∀ p q, 0 ≤ Descent.defect (-(latField s ∘ diamondHom)) p q)
      ∧ ¬ Descent.Realizable (-(latField s ∘ diamondHom)) :=
  not_realizable_neg_diamondHom hs

/-! ## The definiteness bridge -/

example {ι : Type*} (K : ι → ι → ℝ) (P : Finset ι) :
    IsCNDOn K P ↔ Descent.CondNegSemidef (kernelMatrix K P) :=
  isCNDOn_iff_condNegSemidef K P

example (s : ℝ) {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p) :
    kernelMatrix (pairing s) P
      = Descent.defectMatrix (resField theta s) (resSample P) :=
  pairingMatrix_eq_defectMatrix s hpos

example (s : ℝ) {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p) :
    IsCNDOn (pairing s) P
      ↔ Descent.CondNegSemidef
          (Descent.defectMatrix (resField theta s) (resSample P)) :=
  isCNDOn_pairing_iff s hpos

example {s : ℝ} (hs : 1 ≤ s) {P : Finset ℕ}
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    Descent.CondNegSemidef
      (Descent.defectMatrix (resField theta s) (resSample P)) :=
  condNegSemidef_resField_large hs hprime

example (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcard : 3 ≤ P.card) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ¬ Descent.CondNegSemidef
          (Descent.defectMatrix (resField theta s) (resSample P)) :=
  not_condNegSemidef_resField_small P hprime hcard

example {R : Type*} [Lattice R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Descent.ContextField R ℝ} {r : ι → R} {i₀ : ι}
    (hbase : ∀ i, r i₀ ≤ r i) :
    Descent.CondNegSemidef (Descent.defectMatrix K r)
      ↔ Descent.defectMatrix K r = 0 :=
  Descent.condNegSemidef_defectMatrix_iff_of_base hbase

example {s : ℝ} (hs : 0 < s) {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p)
    (h1 : 1 ∈ P) :
    IsCNDOn (pairing s) P ↔ ∀ p ∈ P, ∀ q ∈ P, p ∣ q ∨ q ∣ p :=
  isCNDOn_pairing_iff_chain_of_one_mem hs hpos h1

example {s : ℝ} (hs : 0 < s) {P : Finset ℕ} (hpos : ∀ p ∈ P, 0 < p)
    (h1 : 1 ∈ P) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpP : p ∈ P) (hqP : q ∈ P) :
    ¬ IsCNDOn (pairing s) P :=
  not_isCNDOn_pairing_one_prime_prime hs hpos h1 hp hq hpq hpP hqP

/-! ## The resolution metric -/

example (T : PartitionTower) (hnt : ∃ k : T.Λ, k ≠ T.modal) {β β' : ℝ}
    (hβ : 1 ≤ β) (hlt : β < β') : T.Z β' < T.Z β :=
  T.Z_lt_Z hnt hβ hlt

example (Q : QuadLatticeAction) (hnt : ∃ a : Q.Λ, a ≠ 0) {β β' : ℝ}
    (hβ : 0 < β) (hlt : β < β') :
    Q.scaledPartFn β' < Q.scaledPartFn β :=
  Q.scaledPartFn_lt hnt hβ hlt

example (Z : ℝ → ℝ) (s : ℝ) (n m : ℕ+) :
    Descent.defect (resField Z s) (Descent.Arith.of n) (Descent.Arith.of m)
      = -fieldDefect Z s (n : ℕ) (m : ℕ) :=
  defect_resField Z s n m

example (Z : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (hZ : ∀ β, 0 < β → 0 < Z β)
    (a b : Descent.Arith) :
    resDist Z s a b
      = Real.log
          (Z (((Descent.Arith.num a : ℕ) : ℝ) ^ 2 * s)
              * Z (((Descent.Arith.num b : ℕ) : ℝ) ^ 2 * s)
            / Z (((Nat.lcm (Descent.Arith.num a : ℕ)
                  (Descent.Arith.num b : ℕ) : ℕ) : ℝ) ^ 2 * s) ^ 2) :=
  resDist_eq Z hs hZ a b

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s) :
    Descent.Submodular (resField Q.scaledPartFn s) :=
  submodular_resField Q hs

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s)
    (hnt : ∃ x : Q.Λ, x ≠ 0) :
    StrictMono (resField Q.scaledPartFn s) :=
  strictMono_resField Q hs hnt

noncomputable example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s) :
    PseudoMetricSpace Descent.Arith :=
  resPseudoMetricSpace Q hs

example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s)
    (hnt : ∃ x : Q.Λ, x ≠ 0) (a b : Descent.Arith) :
    resDist Q.scaledPartFn s a b = 0 ↔ a = b :=
  resDist_eq_zero_iff Q hs hnt a b

noncomputable example (Q : QuadLatticeAction) {s : ℝ} (hs : 0 < s)
    (hnt : ∃ x : Q.Λ, x ≠ 0) : MetricSpace Descent.Arith :=
  resMetricSpace Q hs hnt

example (Z : ℝ → ℝ) (s : ℝ) {a b : Descent.Arith} (h : a ≤ b) :
    resDist Z s a b = resField Z s b - resField Z s a :=
  resDist_of_le Z s h

example (s : ℝ) (p q : ℕ+) (hco : Nat.Coprime (p : ℕ) (q : ℕ)) :
    pairing s (p : ℕ) (q : ℕ)
      = resDist theta s (Descent.Arith.of 1) (Descent.Arith.of (p * q))
        - resDist theta s (Descent.Arith.of p) (Descent.Arith.of q) :=
  pairing_eq_resDist_sub s p q hco

example {s : ℝ} (hs : 0 < s) {p q : ℕ+} (hco : Nat.Coprime (p : ℕ) (q : ℕ))
    (hpq : ¬ ((p : ℕ) ∣ (q : ℕ))) (hqp : ¬ ((q : ℕ) ∣ (p : ℕ))) :
    resDist theta s (Descent.Arith.of p) (Descent.Arith.of q)
      < resDist theta s (Descent.Arith.of 1) (Descent.Arith.of (p * q)) :=
  resDist_lt_resDist_base hs hco hpq hqp

/-! ## The scale asymptotics of a Gram Boltzmann sum -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (β : ℝ) :
    (gramTower hM).Z β = gramTheta M β :=
  gramTower_Z hM β

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    Tendsto (gramTheta M) atTop (𝓝 1) :=
  tendsto_gramTheta_atTop hM

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) :
    gramTheta M s
      = (Real.pi / s) ^ ((d : ℝ) / 2) * (M.det⁻¹) ^ ((1 : ℝ) / 2)
        * gramTheta M⁻¹ (Real.pi ^ 2 / s) :=
  gramTheta_eq_dual hM hs

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    Tendsto (fun s : ℝ => (s / Real.pi) ^ ((d : ℝ) / 2) * gramTheta M s)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.det ^ (-(1 : ℝ) / 2))) :=
  tendsto_gramTheta_nhdsGT_zero hM

example {d : ℕ} {M N : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef)
    (hN : N.PosDef) :
    Tendsto (fun s : ℝ => gramTheta M s / gramTheta N s) (𝓝[>] (0 : ℝ))
      (𝓝 ((N.det / M.det) ^ ((1 : ℝ) / 2))) :=
  tendsto_gramTheta_ratio hM hN

/-! ## The finite-index mass ratio -/

example {d : ℕ} {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) :
    ∃ n : ℤ, n.natAbs = H.index ∧ (subChart b).det = (n : ℝ) :=
  natAbs_det_subChart b

example {d : ℕ} {H : AddSubgroup (Fin d → ℤ)} (hidx : H.index ≠ 0)
    (b : Module.Basis (Fin d) ℤ H) : (subGram b).PosDef :=
  subGram_posDef hidx b

example {d : ℕ} {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) :
    (subGram b).det = ((H.index : ℝ)) ^ 2 :=
  det_subGram b

example {d : ℕ} {H : AddSubgroup (Fin d → ℤ)} (s : ℝ)
    (b : Module.Basis (Fin d) ℤ H) :
    subMass s H = gramTheta (subGram b) s :=
  subMass_eq_gramTheta s b

noncomputable example {d : ℕ} {H : AddSubgroup (Fin d → ℤ)}
    (hH : H.index ≠ 0) : Module.Basis (Fin d) ℤ H :=
  subBasis hH

example {d : ℕ} {U V : AddSubgroup (Fin d → ℤ)} (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) :
    Tendsto (fun s => subMass s U / subMass s V) (𝓝[>] (0 : ℝ))
      (𝓝 (((V.relIndex U : ℕ) : ℝ))) :=
  tendsto_subMass_ratio hle hU hV

example {d : ℕ} {U V : AddSubgroup (Fin d → ℤ)} (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) :
    Tendsto (fun s => Real.log (subMass s U) - Real.log (subMass s V))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (((V.relIndex U : ℕ) : ℝ)))) :=
  tendsto_log_subMass_sub hle hU hV

/-! ## The pairwise boundary of the sublattice field -/

example {d : ℕ} {A B : AddSubgroup (Fin d → ℤ)} (hA : A.index ≠ 0)
    (hB : B.index ≠ 0) :
    Tendsto (fun s => Descent.defect (subField s) A B) (𝓝[>] (0 : ℝ))
      (𝓝 0) :=
  tendsto_defect_subField hA hB

example {d : ℕ} (A B C : AddSubgroup (Fin d → ℤ)) :
    distribLower A B C ≤ distribUpper A B C :=
  distribLower_le_upper A B C

example {d : ℕ} {A B C : AddSubgroup (Fin d → ℤ)} (hA : A.index ≠ 0)
    (hB : B.index ≠ 0) (hC : C.index ≠ 0) :
    Tendsto (fun s => Descent.defect3 (subField s) A B C) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log ((((distribLower A B C).relIndex
        (distribUpper A B C) : ℕ)) : ℝ))) :=
  tendsto_defect3_subField hA hB hC

/-! ## The strict maximum of the shifted Gaussian mass -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    gramMass M α x ≤ gramMass M α 0 :=
  gramMass_le_gramMass_zero hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {x : Fin d → ℝ} (hx : ¬ IsLatticeShift x) :
    gramMass M α x < gramMass M α 0 :=
  gramMass_lt_gramMass_zero hM hα hx

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    gramMass M α x = gramMass M α 0 ↔ IsLatticeShift x :=
  gramMass_eq_gramMass_zero_iff hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (z : Fin d → ℝ) (c : Fin d → ZMod 2) :
    parityVector M α z c = gramMass M (2 * α) 0
      ↔ IsLatticeShift ((2 : ℝ)⁻¹ • (z + fun i => ((c i).val : ℝ))) :=
  parityVector_eq_max_iff hM hα z c

example {d : ℕ} {n : ℕ} (hn : 0 < n) (c : Fin d → ZMod n) :
    IsLatticeShift (residueShift n c) ↔ c = 0 :=
  isLatticeShift_residueShift_iff hn c

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {s : ℝ}
    (hs : 0 < s) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : TwoGridReflection M s a b) {r : Fin d → ZMod b}
    {c : Fin d → ZMod a} (hc : c ≠ 0) (e : Fin d → ZMod 2) :
    parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
          (residueShift b r + residueShift a c) e
        < gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0
      ∧ parityVector M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))
          (residueShift b r - residueShift a c) e
        < gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) 0 :=
  twoGridReflection_lt_max hM hs ha hb h hc e

/-! ## Separation of the parity feature vectors -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hd : 0 < d) {s : ℝ}
    {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hsep : ParitySeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    ¬ TwoGridReflection M s a b :=
  not_twoGridReflection_of_paritySeparating hd ha hb hsep

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (hsep : ParitySeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 :=
  gramDefect_neg_of_paritySeparating hM hd hs ha hb hco hsep

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) (α : ℝ) (z : Fin d → ℝ)
    (c : Fin d → ZMod 2) :
    parityVector M α (flipCoords T z) c = parityVector M α z c :=
  parityVector_flipCoords hT α z c

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) (α : ℝ) : ¬ ParitySeparating M α :=
  not_paritySeparating_of_split hT hi₀ hj₀ α

/-! ## The real Gaussian core of separation -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {z w : Fin d → ℝ}
    (h : parityVector M α z = parityVector M α w) (u : Fin d → ℝ) :
    gramMass M α ((2 : ℝ)⁻¹ • (z + u))
        * gramMass M α ((2 : ℝ)⁻¹ • (z - u))
      = gramMass M α ((2 : ℝ)⁻¹ • (w + u))
        * gramMass M α ((2 : ℝ)⁻¹ • (w - u)) :=
  gramMass_reflect_prod_of_parityVector_eq hM hα h u

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {z w : Fin d → ℝ}
    (h : parityVector M α z = parityVector M α w) (v : Fin d → ℝ) :
    logMass M α ((2 : ℝ)⁻¹ • z + v) + logMass M α ((2 : ℝ)⁻¹ • z - v)
      = logMass M α ((2 : ℝ)⁻¹ • w + v)
        + logMass M α ((2 : ℝ)⁻¹ • w - v) :=
  logMass_even_part_eq_of_parityVector_eq hM hα h v

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (h : EvenPartSeparating M α) : ParitySeparating M α :=
  paritySeparating_of_evenPartSeparating hM hα h

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (h : EvenPartSeparating M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 :=
  gramDefect_neg_of_evenPartSeparating hM hd hs ha hb hco h

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) : ¬ EvenPartSeparating M α :=
  not_evenPartSeparating_of_split hM hα hT hi₀ hj₀

example {d : ℕ} {p q : Fin d → ℝ}
    (h1 : ∀ i, (∃ k : ℤ, p i = (k : ℝ)) ∨ (∃ k : ℤ, q i = (k : ℝ)))
    (h2 : ∀ i j, i ≠ j → (∃ k : ℤ, p i + p j = (k : ℝ))
      ∨ (∃ k : ℤ, q i + q j = (k : ℝ))) :
    IsLatticeShift p ∨ IsLatticeShift q :=
  isLatticeShift_or_of_pairwise h1 h2

/-! ## The torus Fourier coefficients of the logarithmic mass -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (α : ℝ) (x : Fin d → ℝ) :
    logMassTorus M α (torusMk x) = logMass M α x :=
  logMassTorus_mk M α x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) : Continuous (logMassTorus M α) :=
  continuous_logMassTorus hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (α : ℝ) (ν : Fin d → ℤ) :
    logMassCoeff M α (-ν) = logMassCoeff M α ν :=
  logMassCoeff_neg M α ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (α : ℝ) (ν : Fin d → ℤ) :
    (starRingEnd ℂ) (logMassCoeff M α ν) = logMassCoeff M α (-ν) :=
  logMassCoeff_conj M α ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (α : ℝ) (ν : Fin d → ℤ) :
    logMassCoeff M α ν = ((logMassRe M α ν : ℝ) : ℂ) :=
  logMassCoeff_eq_ofReal M α ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {a b : Fin d → ℝ}
    (h : ∀ v : Fin d → ℝ, logMass M α (a + v) + logMass M α (a - v)
      = logMass M α (b + v) + logMass M α (b - v)) (ν : Fin d → ℤ) :
    logMassRe M α ν * (2 * Real.cos (2 * Real.pi * dualPairing ν a))
      = logMassRe M α ν * (2 * Real.cos (2 * Real.pi * dualPairing ν b)) :=
  logMassCoeff_cos_eq hM hα h ν

example {d : ℕ} (i : Fin d) (x : Fin d → ℝ) :
    dualPairing (freqSingle i) x = x i :=
  dualPairing_freqSingle i x

example {d : ℕ} (i j : Fin d) (x : Fin d → ℝ) :
    dualPairing (freqPair i j) x = x i + x j :=
  dualPairing_freqPair i j x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hc : FiniteCertificate M α) : EvenPartSeparating M α :=
  evenPartSeparating_of_finiteCertificate hM hα hc

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) {T : Finset (Fin d)}
    (hT : ∀ i j, (i ∈ T) ≠ (j ∈ T) → M i j = 0) {i₀ j₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hj₀ : j₀ ∉ T) : ¬ FiniteCertificate M α :=
  not_finiteCertificate_of_split hM hα hT hi₀ hj₀

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (hd : 0 < d)
    {s : ℝ} (hs : 0 < s) {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hco : Nat.Coprime a b)
    (hcert : FiniteCertificate M ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) :
    gramDefect M s a b < 0 :=
  gramDefect_neg_of_finiteCertificate hM hd hs ha hb hco hcert

/-! ## The cluster normalization of the logarithmic mass -/

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    gramMass M α x = zeroMode M α * (1 + residual M α x) :=
  gramMass_eq_zeroMode_mul hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        if m = 0 then 0
        else modeWeight M α m * Real.cos (2 * Real.pi * dualPairing m x))
      (residual M α x) :=
  hasSum_residual hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℝ) :
    |residual M α x| ≤ totalWeight M α :=
  abs_residual_le_totalWeight hM hα x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) :
    HasSum (fun m : Fin d → ℤ => if m = 0 then 0 else modeWeight M α m)
      (totalWeight M α) :=
  hasSum_totalWeight hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) :
    totalWeight M α
      = (α / Real.pi) ^ ((d : ℝ) / 2) * gramTheta M α
          * M.det ^ ((1 : ℝ) / 2) - 1 :=
  totalWeight_eq_scaled hM hα

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    Tendsto (fun α : ℝ => totalWeight M α) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_totalWeight_nhdsGT_zero hM

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ α in 𝓝[>] (0 : ℝ), totalWeight M α < ε :=
  eventually_totalWeight_lt hM hε

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) (x : Fin d → ℝ) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1))
      (logMass M α x - Real.log (zeroMode M α)) :=
  hasSum_logMass_residual hM hα hw x

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) (K : ℕ) (x : Fin d → ℝ) :
    |logMass M α x - Real.log (zeroMode M α)
        - ∑ k ∈ Finset.range K,
            (-1 : ℝ) ^ k * residual M α x ^ (k + 1) / (k + 1)|
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) :=
  abs_logMass_sub_partialSum_le hM hα hw K x

/-! ## The cluster expansion on Fourier coefficients -/

example {d : ℕ} (κ : Fin d → ℤ) :
    (∫ z : UnitAddTorus (Fin d), mFourier κ z
        ∂(MeasureTheory.Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
      = if κ = 0 then 1 else 0 :=
  integral_mFourier κ

example {d : ℕ} (m ν : Fin d → ℤ) :
    mFourierCoeff (fun z => mFourier m z) ν = if m = ν then 1 else 0 :=
  mFourierCoeff_mFourier m ν

example {d : ℕ} {a : (Fin d → ℤ) → ℂ} {f : UnitAddTorus (Fin d) → ℂ}
    (h : HasCharSum a f) (ν : Fin d → ℤ) : mFourierCoeff f ν = a ν :=
  h.mFourierCoeff_eq ν

example {d : ℕ} {a b : (Fin d → ℤ) → ℂ} {f g : UnitAddTorus (Fin d) → ℂ}
    (ha : HasCharSum a f) (hb : HasCharSum b g) :
    HasCharSum (convolve a b) (fun z => f z * g z) :=
  ha.mul hb

example {d : ℕ} {a : (Fin d → ℤ) → ℂ} {f : UnitAddTorus (Fin d) → ℂ}
    (ha : HasCharSum a f) (k : ℕ) :
    HasCharSum (convPow a k) (fun z => f z ^ (k + 1)) :=
  ha.pow k

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) :
    HasCharSum (modeCoeff M α)
      (fun z => ((residualTorus M α z : ℝ) : ℂ)) :=
  hasCharSum_residual hM hα

example {d : ℕ} {f : UnitAddTorus (Fin d) → ℂ} {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (ν : Fin d → ℤ) : ‖mFourierCoeff f ν‖ ≤ C :=
  norm_mFourierCoeff_le hC ν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) (K : ℕ) {ν : Fin d → ℤ}
    (hν : ν ≠ 0) :
    ‖logMassCoeff M α ν - clusterPartial M α K ν‖
      ≤ totalWeight M α ^ (K + 1) / (1 - totalWeight M α) :=
  norm_logMassCoeff_sub_clusterPartial_le hM hα hw K hν

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ}
    (hα : 0 < α) (hw : totalWeight M α < 1) {ν : Fin d → ℤ} (hν : ν ≠ 0) :
    ‖logMassCoeff M α ν
        - (modeCoeff M α ν
          - (1 / 2) * convolve (modeCoeff M α) (modeCoeff M α) ν)‖
      ≤ totalWeight M α ^ 3 / (1 - totalWeight M α) :=
  norm_logMassCoeff_sub_second_order_le hM hα hw hν

example {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (U : GL (Fin n) ℤ) (m : ℤ) :
    (classPairs ((U : Matrix (Fin n) (Fin n) ℤ)ᵀ * G *
      (U : Matrix (Fin n) (Fin n) ℤ)) m).ncard = (classPairs G m).ncard :=
  classPairs_ncard_eq_of_isometry G U m

example : (classPairs schiemannA 12).ncard = 10 ∧ (classPairs schiemannB 12).ncard = 18 :=
  ⟨schiemannA_classPairs_ncard, schiemannB_classPairs_ncard⟩

example : ¬ ∃ U : GL (Fin 4) ℤ, (U : Matrix (Fin 4) (Fin 4) ℤ)ᵀ * schiemannA *
    (U : Matrix (Fin 4) (Fin 4) ℤ) = schiemannB :=
  schiemann_not_isometric

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (y : Fin d → ℝ) :
    twistTheta M⁻¹ y (Real.pi ^ 2 / α)
      = (α / Real.pi) ^ ((d : ℝ) / 2) * M.det ^ ((1 : ℝ) / 2) * gramMass M α y :=
  gramMass_dual hM hα y

example {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (c : Fin d → ℤ) {s : ℝ}
    (hs : 0 < s) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') :
    fieldDefect (cosetMass M c) s q q'
      = fieldDefect (twistTheta M⁻¹ (halfShift c))
          (Real.pi ^ 2 / (4 * (Nat.lcm q q' : ℝ) ^ 2 * s))
          (q / Nat.gcd q q') (q' / Nat.gcd q q') :=
  cosetDefect_dual hM c hs hq hq'

example : 0 < fieldDefect (cosetMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ![1]) 1 2 3 :=
  cosetDefect_odd_pos

example : ∃ T, IsEmpty (siegelSet schiemannA T ≃ siegelSet schiemannB T) :=
  schiemann_siegelSet_ne

example {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hG : EvenPosForm G)
    (S : Finset (Fin n → ℤ)) (hS : ∀ x ∈ S, intEnergy G x = 4)
    (hc : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (2 : ℤ) ∣ x i - y i) : S.card ≤ 2 * n :=
  frame_card_le hG S hS hc

example : ¬ ∃ U : GL (Fin 16) ℤ, (U : Matrix (Fin 16) (Fin 16) ℤ)ᵀ * e8sq *
    (U : Matrix (Fin 16) (Fin 16) ℤ) = d16plus :=
  e8sq_not_isometric_d16plus

end Theaetetus
