import Theaetetus.Kernel
import Theaetetus.LargeScale

/-! # The small-scale chamber: no three primes stay CND

**The degenerate chamber.** As `s → 0` the reflection
law evaluates each coprime entry at its own dual scale
`σ = π²/(s·p²q²)`, and the entries separate exponentially: the
pair with the largest product dominates every other. For an
ordered triple `p < q < r` the combined deep-scale limit

    e^τ·(⟨q,r⟩_τ − 2·⟨p,q⟩_{(r/p)²τ} − 2·⟨p,r⟩_{(q/p)²τ}) → 2

(`eventually_pairing_dominates`) gives eventual dominance, the
reflection `pairing_scale_even` transports it to a small-scale
threshold (`pairing_dominates_small`), and the zero-sum weight
`(−2, 1, 1)` turns dominance into a positive quadratic form
(`quadFormOn_triple`): the triple is not CND
(`pairing_not_cnd_small`, through `IsCNDOn.subset` for every
finite prime set with at least three elements). The analytic
argument and the finite-set combinatorics stay separated: the
limit does the analysis once, the weight does the algebra once. -/

namespace Theaetetus

open Filter Topology

/-- **Dominance at deep scale**: for an ordered coprime triple
`p < q < r`, eventually along `τ → ∞` the top pairing beats twice
the sum of the other two, each evaluated at its ratio-shifted
scale. -/
theorem eventually_pairing_dominates {p q r : ℕ} (hp : 2 ≤ p)
    (hpq : p < q) (hqr : q < r) (hcpq : Nat.Coprime p q)
    (hcpr : Nat.Coprime p r) (hcqr : Nat.Coprime q r) :
    ∀ᶠ τ in atTop,
      2 * pairing (((r : ℝ) / (p : ℝ)) ^ 2 * τ) p q
        + 2 * pairing (((q : ℝ) / (p : ℝ)) ^ 2 * τ) p r
      < pairing τ q r := by
  have hq2 : 2 ≤ q := by omega
  have hr2 : 2 ≤ r := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpqR : ((p : ℝ)) < (q : ℝ) := by exact_mod_cast hpq
  have hprR : ((p : ℝ)) < (r : ℝ) := by exact_mod_cast (by omega : p < r)
  have hc1 : (1 : ℝ) < ((r : ℝ) / (p : ℝ)) ^ 2 := by
    have h1 : (1 : ℝ) < (r : ℝ) / (p : ℝ) := (one_lt_div hpR).mpr hprR
    nlinarith
  have hc2 : (1 : ℝ) < ((q : ℝ) / (p : ℝ)) ^ 2 := by
    have h1 : (1 : ℝ) < (q : ℝ) / (p : ℝ) := (one_lt_div hpR).mpr hpqR
    nlinarith
  have h := ((tendsto_exp_mul_pairing hq2 hr2 hcqr).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_exp_mul_pairing_shift hc1 hp hq2 hcpq))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_exp_mul_pairing_shift hc2 hp hr2 hcpr))
  norm_num at h
  have hpos := h.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hpos] with τ hτ
  have hexp : (0 : ℝ) < Real.exp τ := Real.exp_pos τ
  have h2 : Real.exp τ
        * (2 * pairing (((r : ℝ) / (p : ℝ)) ^ 2 * τ) p q
          + 2 * pairing (((q : ℝ) / (p : ℝ)) ^ 2 * τ) p r)
      < Real.exp τ * pairing τ q r := by nlinarith [hτ]
  exact lt_of_mul_lt_mul_left h2 hexp.le

/-- **The small-scale threshold**: for an ordered coprime triple
there is an `ε > 0` below which, at every scale, the top pairing
beats twice the sum of the other two — the reflection of the
deep-scale dominance through `pairing_scale_even`. -/
theorem pairing_dominates_small {p q r : ℕ} (hp : 2 ≤ p)
    (hpq : p < q) (hqr : q < r) (hcpq : Nat.Coprime p q)
    (hcpr : Nat.Coprime p r) (hcqr : Nat.Coprime q r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      2 * pairing s p q + 2 * pairing s p r < pairing s q r := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_pairing_dominates hp hpq hqr hcpq hcpr hcqr)
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hr0 : 0 < r := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hT'0 : (0 : ℝ) < max T 1 := lt_of_lt_of_le one_pos (le_max_right T 1)
  refine ⟨Real.pi ^ 2 / (((q : ℝ) * (r : ℝ)) ^ 2 * max T 1),
    by positivity, fun s hs hsε => ?_⟩
  -- the dual scale exceeds the dominance threshold
  have hA : (0 : ℝ) < ((q : ℝ) * (r : ℝ)) ^ 2 * max T 1 := by positivity
  have h1 : s * (((q : ℝ) * (r : ℝ)) ^ 2 * max T 1) < Real.pi ^ 2 :=
    (lt_div_iff₀ hA).mp hsε
  have hτ : max T 1 < Real.pi ^ 2 / (((q : ℝ) * (r : ℝ)) ^ 2 * s) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [h1]
  have hτT : T ≤ Real.pi ^ 2 / (((q : ℝ) * (r : ℝ)) ^ 2 * s) :=
    le_trans (le_max_left T 1) hτ.le
  have key := hT _ hτT
  -- reflect the three entries from scale s to their dual scales
  have harg1 : ((r : ℝ) / (p : ℝ)) ^ 2
        * (Real.pi ^ 2 / (((q : ℝ) * (r : ℝ)) ^ 2 * s))
      = Real.pi ^ 2 / (((p : ℝ) * (q : ℝ)) ^ 2 * s) := by
    field_simp
  have harg2 : ((q : ℝ) / (p : ℝ)) ^ 2
        * (Real.pi ^ 2 / (((q : ℝ) * (r : ℝ)) ^ 2 * s))
      = Real.pi ^ 2 / (((p : ℝ) * (r : ℝ)) ^ 2 * s) := by
    field_simp
  rw [harg1, harg2] at key
  rw [pairing_scale_even hs hp0 hq0 hcpq, pairing_scale_even hs hp0 hr0 hcpr,
    pairing_scale_even hs hq0 hr0 hcqr]
  exact key

/-- The `(−2, 1, 1)` weight on an ordered triple reduces the
quadratic form to twice the dominance bracket. -/
theorem quadFormOn_triple (s : ℝ) {p q r : ℕ} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    quadFormOn (pairing s) {p, q, r}
      (fun n => if n = p then -2 else if n = q then 1 else
        if n = r then 1 else 0)
    = 2 * (pairing s q r - 2 * pairing s p q - 2 * pairing s p r) := by
  have hqp : q ≠ p := hpq.symm
  have hrp : r ≠ p := hpr.symm
  have hrq : r ≠ q := hqr.symm
  have hpmem : p ∉ ({q, r} : Finset ℕ) := by simp [hpq, hpr]
  have hqmem : q ∉ ({r} : Finset ℕ) := by simp [hqr]
  unfold quadFormOn
  simp only [Finset.sum_insert hpmem, Finset.sum_insert hqmem,
    Finset.sum_singleton, hpq, hpr, hqr, hqp, hrp, hrq, ite_true, ite_false,
    pairing_self, mul_zero]
  rw [pairing_comm s q p, pairing_comm s r p, pairing_comm s r q]
  ring

/-- A finite set of naturals with at least three elements contains
an ordered triple: successive minima. -/
theorem exists_ordered_triple {P : Finset ℕ} (h : 3 ≤ P.card) :
    ∃ p ∈ P, ∃ q ∈ P, ∃ r ∈ P, p < q ∧ q < r := by
  have h0 : P.Nonempty := Finset.card_pos.mp (by omega)
  have hpP : P.min' h0 ∈ P := P.min'_mem h0
  have h1 : (P.erase (P.min' h0)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hpP]; omega
  have hqE := Finset.min'_mem _ h1
  have hqP : (P.erase (P.min' h0)).min' h1 ∈ P := Finset.mem_of_mem_erase hqE
  have hpq : P.min' h0 < (P.erase (P.min' h0)).min' h1 :=
    lt_of_le_of_ne (P.min'_le _ hqP) (Finset.ne_of_mem_erase hqE).symm
  have h2 : ((P.erase (P.min' h0)).erase
      ((P.erase (P.min' h0)).min' h1)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hqE,
      Finset.card_erase_of_mem hpP]
    omega
  have hrE := Finset.min'_mem _ h2
  have hrE1 := Finset.mem_of_mem_erase hrE
  have hrP : _ ∈ P := Finset.mem_of_mem_erase hrE1
  have hqr : (P.erase (P.min' h0)).min' h1
      < ((P.erase (P.min' h0)).erase ((P.erase (P.min' h0)).min' h1)).min' h2 :=
    lt_of_le_of_ne ((P.erase (P.min' h0)).min'_le _ hrE1)
      (Finset.ne_of_mem_erase hrE).symm
  exact ⟨_, hpP, _, hqP, _, hrP, hpq, hqr⟩

/-- **THE SMALL-SCALE CHAMBER**: every finite set of at
least three primes fails conditional negative definiteness at all
sufficiently small scales. The dual scales separate the entries
exponentially, the largest product dominates, and the `(−2, 1, 1)`
weight on the bottom triple exposes it; `IsCNDOn.subset` lifts the
failure from the triple to the whole set. -/
theorem pairing_not_cnd_small (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hcard : 3 ≤ P.card) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ¬ IsCNDOn (pairing s) P := by
  obtain ⟨p, hpP, q, hqP, r, hrP, hpq, hqr⟩ := exists_ordered_triple hcard
  have hp2 : 2 ≤ p := (hprime p hpP).two_le
  have hcpq : Nat.Coprime p q :=
    (Nat.coprime_primes (hprime p hpP) (hprime q hqP)).mpr hpq.ne
  have hcpr : Nat.Coprime p r :=
    (Nat.coprime_primes (hprime p hpP) (hprime r hrP)).mpr (by omega)
  have hcqr : Nat.Coprime q r :=
    (Nat.coprime_primes (hprime q hqP) (hprime r hrP)).mpr hqr.ne
  obtain ⟨ε, hε0, hdom⟩ :=
    pairing_dominates_small hp2 hpq hqr hcpq hcpr hcqr
  refine ⟨ε, hε0, fun s hs hsε hCND => ?_⟩
  have hsub : ({p, q, r} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have htri := hCND.subset hsub
  have hpmem : p ∉ ({q, r} : Finset ℕ) := by
    simp [hpq.ne, (hpq.trans hqr).ne]
  have hqmem : q ∉ ({r} : Finset ℕ) := by simp [hqr.ne]
  have hsum : (∑ x ∈ ({p, q, r} : Finset ℕ),
      (fun n => if n = p then (-2 : ℝ) else if n = q then 1 else
        if n = r then 1 else 0) x) = 0 := by
    rw [Finset.sum_insert hpmem, Finset.sum_insert hqmem,
      Finset.sum_singleton]
    simp [hpq.ne', hqr.ne', ((hpq.trans hqr).ne).symm]
    norm_num
  have hquad := htri _ hsum
  rw [quadFormOn_triple s hpq.ne (hpq.trans hqr).ne hqr.ne] at hquad
  have hd := hdom s hs hsε
  linarith

end Theaetetus
