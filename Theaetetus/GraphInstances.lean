import Theaetetus.GraphHomology
import Theaetetus.ThetaGraph
import Theaetetus.Periods

/-! # Concrete Graph Topology: bases for the cycle and theta graphs

The concrete carriers' lattice bases, through the pure
graph-homology layer:

* `cycleLatticeBasis` — the all-ones cycle as a genuine
  `Module.Basis (Fin 1) ℤ` of `H₁(C_n; ℤ)`, giving `b₁ = 1`
  through `card_eq_b1` (`cycleGraph_b1'`).
* `thetaLatticeBasis` — the two path-differences `c₁ = p₁ − p₃`,
  `c₂ = p₂ − p₃` as a `ℤ`-basis of `H₁(K₂,₃; ℤ)`, giving `b₁ = 2`
  (`thetaGraph_b1'`).
* the cast forms `cyclesR_cycleLatticeBasis` /
  `cyclesR_thetaLatticeBasis` feeding the priced (Gram) layer. -/

namespace Theaetetus

open scoped BigOperators

universe u

/-! ## The cycle graph -/

/-- The cycle graph's boundary in closed form: inflow minus outflow —
over any commutative ring. -/
theorem cycleGraph_boundary_eq {R : Type*} [CommRing R]
    (n : ℕ) (hn : 0 < n) [NeZero n] (ω : Fin n → R) (v : Fin n) :
    (cycleGraph n hn).boundary ω v = ω (v - 1) - ω v := by
  show ∑ e : Fin n, ((if e + 1 = v then (1 : R) else 0)
    - (if e = v then (1 : R) else 0)) * ω e = ω (v - 1) - ω v
  rw [show (fun e : Fin n => ((if e + 1 = v then (1 : R) else 0)
      - (if e = v then (1 : R) else 0)) * ω e)
      = fun e => ((if e = v - 1 then ω e else 0) - if e = v then ω e else 0) from
    funext fun e => by
      by_cases h1 : e + 1 = v
      · have h1' : e = v - 1 := by rw [eq_sub_iff_add_eq]; exact h1
        by_cases h2 : e = v
        · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1', ite_eq_left h2]; ring
        · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1', ite_eq_right h2]; ring
      · have h1' : ¬(e = v - 1) := fun hc =>
          h1 (by rw [← eq_sub_iff_add_eq]; exact hc)
        by_cases h2 : e = v
        · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1', ite_eq_left h2]; ring
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1', ite_eq_right h2]; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (v - 1) ω,
    Finset.sum_ite_eq' Finset.univ v ω]
  simp

/-- The integral basis cycle of `C_n`: the all-ones cochain. -/
def cycleCyclesZ (n : ℕ) : Fin 1 → Fin n → ℤ := fun _ _ => 1

/-- The all-ones cochain is an integral cycle. -/
theorem cycleCyclesZ_mem (n : ℕ) (hn : 0 < n) (i : Fin 1) :
    cycleCyclesZ n i ∈ (cycleGraph n hn).cycleLattice := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [IncidenceGraph.mem_cycleLattice]
  intro v
  rw [cycleGraph_boundary_eq]
  show (1 : ℤ) - 1 = 0
  ring

/-- **A closed cochain on `C_n` is constant**: flow conservation
around the cycle equalizes consecutive edges. -/
theorem eq_const_of_cycle_boundary_eq_zero (n : ℕ) (hn : 0 < n)
    [NeZero n] (ω : Fin n → ℝ)
    (h : ∀ v, (cycleGraph n hn).boundary ω v = 0) :
    ω = fun _ => ω 0 := by
  have hstep : ∀ v : Fin n, ω (v - 1) = ω v := by
    intro v
    have := h v
    rw [cycleGraph_boundary_eq] at this
    linarith
  have hsucc : ∀ v : Fin n, ω v = ω (v + 1) := fun v => by
    have := hstep (v + 1)
    rwa [add_sub_cancel_right] at this
  have hval : ∀ (m : ℕ) (hm : m < n), ω ⟨m, hm⟩ = ω 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
      rw [h0]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmk : (⟨m + 1, hm⟩ : Fin n) = ⟨m, hm'⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add]
        have h1 : (1 : Fin n).val = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt hm).symm
      rw [hmk, ← hsucc ⟨m, hm'⟩]
      exact ih hm'
  funext e
  rw [show e = ⟨e.val, e.isLt⟩ from (Fin.eta e e.isLt).symm,
    hval e.val e.isLt]

/-- Independence of the cast all-ones cycle. -/
theorem cycle_cast_independent (n : ℕ) (hn : 0 < n) (x : Fin 1 → ℝ)
    (hx : (fun e => ∑ i, x i * ((cycleCyclesZ n i e : ℤ) : ℝ)) = 0) :
    x = 0 := by
  have h0 := congrFun hx ⟨0, hn⟩
  rw [Fin.sum_univ_one] at h0
  have hx0 : x 0 = 0 := by
    have : x 0 * ((1 : ℤ) : ℝ) = 0 := h0
    simpa using this
  funext i
  fin_cases i
  exact hx0

/-- **Integral spanning for `C_n`**: an integral cycle is a constant
integer multiple of the all-ones cycle. -/
theorem cycle_integral_spanning (n : ℕ) (hn : 0 < n) (x : Fin n → ℤ)
    (hx : x ∈ (cycleGraph n hn).cycleLattice) :
    ∃ a : Fin 1 → ℤ, x = fun e => ∑ i, a i * cycleCyclesZ n i e := by
  have : NeZero n := ⟨hn.ne'⟩
  have hclosed : ∀ v,
      (cycleGraph n hn).boundary (fun e => ((x e : ℤ) : ℝ)) v = 0 := by
    intro v
    rw [(cycleGraph n hn).boundary_castR,
      (IncidenceGraph.mem_cycleLattice _ |>.mp hx) v, Int.cast_zero]
  have hr := eq_const_of_cycle_boundary_eq_zero n hn
    (fun e => ((x e : ℤ) : ℝ)) hclosed
  refine ⟨![x 0], ?_⟩
  funext e
  apply Int.cast_injective (α := ℝ)
  have he := congrFun hr e
  rw [he]
  push_cast
  rw [Fin.sum_univ_one]
  show ((x 0 : ℤ) : ℝ) = ((x 0 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)
  simp

/-- **The cycle graph's lattice basis**: the all-ones cycle, as a
genuine `ℤ`-basis of `H₁(C_n; ℤ)`. -/
noncomputable def cycleLatticeBasis (n : ℕ) (hn : 0 < n) :
    Module.Basis (Fin 1) ℤ (cycleGraph n hn).cycleLattice :=
  (cycleGraph n hn).basisOfCycles (cycleCyclesZ n)
    (cycleCyclesZ_mem n hn) (cycle_cast_independent n hn)
    (cycle_integral_spanning n hn)

/-- The basis's integer cycles are the all-ones family. -/
theorem cyclesZ_cycleLatticeBasis (n : ℕ) (hn : 0 < n) :
    (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) = cycleCyclesZ n :=
  (cycleGraph n hn).cyclesZ_basisOfCycles _ _ _ _

/-- `b₁(C_n) = 1` **through the basis** — by `card_eq_b1`. -/
theorem cycleGraph_b1' (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).b1 = 1 :=
  ((cycleGraph n hn).card_eq_b1 (cycleLatticeBasis n hn)).symm

/-- The cast cycles of the cycle graph's lattice basis are the
all-ones family. -/
theorem cyclesR_cycleLatticeBasis (n : ℕ) (hn : 0 < n) :
    (cycleGraph n hn).cyclesR (cycleLatticeBasis n hn) = cycleAllOnes n := by
  funext i e
  show (((cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) i e : ℤ) : ℝ) = 1
  rw [cyclesZ_cycleLatticeBasis]
  exact Int.cast_one

/-! ## The theta graph -/

/-- **The theta graph's lattice basis**: the two path-differences
`c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`, as a genuine `ℤ`-basis of
`H₁(K₂,₃; ℤ)` — assembled from the raw facts of the theta
substrate. -/
noncomputable def thetaLatticeBasis :
    Module.Basis (Fin 2) ℤ thetaGraph.cycleLattice :=
  thetaGraph.basisOfCycles thetaCyclesZ thetaCyclesZ_mem
    theta_cast_independent theta_integral_spanning

/-- The basis's integer cycles are the theta cycles. -/
theorem cyclesZ_thetaLatticeBasis :
    thetaGraph.cyclesZ thetaLatticeBasis = thetaCyclesZ :=
  thetaGraph.cyclesZ_basisOfCycles _ _ _ _

/-- `b₁(K₂,₃) = 2` **through the basis** — by `card_eq_b1`. -/
theorem thetaGraph_b1' : thetaGraph.b1 = 2 :=
  (thetaGraph.card_eq_b1 thetaLatticeBasis).symm

/-- The cast cycles of the theta graph's lattice basis are the cast
theta cycles. (Native addition, for the rank-two carrier.) -/
theorem cyclesR_thetaLatticeBasis :
    thetaGraph.cyclesR thetaLatticeBasis
      = fun i e => ((thetaCyclesZ i e : ℤ) : ℝ) := by
  funext i e
  show ((thetaGraph.cyclesZ thetaLatticeBasis i e : ℤ) : ℝ) = _
  rw [cyclesZ_thetaLatticeBasis]

end Theaetetus
