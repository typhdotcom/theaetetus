import Theaetetus.Theta

/-! # The rank-one defect

For a scale `s > 0` and resolutions `q, q′`, **the defect** is the
four-term inclusion–exclusion of description costs over the
divisibility lattice (README: the seed):

    D_s(q, q′) = [log θ(q²s) + log θ(q′²s)]
                   − [log θ(gcd²s) + log θ(lcm²s)].

Writing `h(q) := log θ(q²s)`, the statement `D ≡ 0` says `h` is a
valuation on the divisibility lattice — the algebraic shadow of an
Euler product. This file proves the boundary: **the defect vanishes
on chains** (`defect_eq_zero_of_dvd`). The witness that it is
strictly negative off them is M2; its sign for all `s` is M3. -/

namespace Theaetetus

/-- **The rank-one defect** `D_s(q, q′)`: the four-term
inclusion–exclusion of log-theta costs over the interval
`[gcd(q,q′), lcm(q,q′)]` of the divisibility lattice. -/
noncomputable def defect (s : ℝ) (q q' : ℕ) : ℝ :=
  (Real.log (theta ((q : ℝ) ^ 2 * s)) + Real.log (theta ((q' : ℝ) ^ 2 * s)))
    - (Real.log (theta ((Nat.gcd q q' : ℝ) ^ 2 * s))
      + Real.log (theta ((Nat.lcm q q' : ℝ) ^ 2 * s)))

/-- The defect is symmetric in its resolutions. -/
theorem defect_comm (s : ℝ) (q q' : ℕ) : defect s q q' = defect s q' q := by
  unfold defect
  rw [Nat.gcd_comm, Nat.lcm_comm]
  ring

/-- **The defect vanishes on chains**: along a divisibility relation
`q ∣ q′` the pair `{gcd, lcm}` collapses to `{q, q′}` and the
four-term combination cancels identically — no positivity of `s`
needed. -/
theorem defect_eq_zero_of_dvd (s : ℝ) {q q' : ℕ} (hdvd : q ∣ q') :
    defect s q q' = 0 := by
  unfold defect
  rw [Nat.gcd_eq_left hdvd,
    Nat.dvd_antisymm (Nat.lcm_dvd hdvd dvd_rfl) (Nat.dvd_lcm_right q q')]
  ring

/-- The diagonal is a chain: `D_s(q, q) = 0`. -/
theorem defect_self (s : ℝ) (q : ℕ) : defect s q q = 0 :=
  defect_eq_zero_of_dvd s dvd_rfl

end Theaetetus
