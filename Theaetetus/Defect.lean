import Theaetetus.Theta
import Theaetetus.FieldDefect

/-! # The rank-one defect

For a scale `s > 0` and resolutions `q, q′`, **the defect** is the
four-term inclusion–exclusion of description costs over the
divisibility lattice:

    D_s(q, q′) = [log θ(q²s) + log θ(q′²s)]
                   − [log θ(gcd²s) + log θ(lcm²s)].

Writing `h(q) := log θ(q²s)`, the statement `D ≡ 0` says `h` is a
valuation on the divisibility lattice — the algebraic shadow of an
Euler product. This file proves the boundary: **the defect vanishes
on chains** (`defect_eq_zero_of_dvd`). That it is strictly
negative off them, at every scale, is the sign theorem
(`defect_neg_of_incomparable`). -/

namespace Theaetetus

/-- **The rank-one defect** `D_s(q, q′)`: the four-term
inclusion–exclusion of log-theta costs over the interval
`[gcd(q,q′), lcm(q,q′)]` of the divisibility lattice. -/
noncomputable def defect (s : ℝ) (q q' : ℕ) : ℝ :=
  (Real.log (theta ((q : ℝ) ^ 2 * s)) + Real.log (theta ((q' : ℝ) ^ 2 * s)))
    - (Real.log (theta ((Nat.gcd q q' : ℝ) ^ 2 * s))
      + Real.log (theta ((Nat.lcm q q' : ℝ) ^ 2 * s)))

/-- The scalar instance of the field defect: the defect is the
field defect of the theta function. -/
theorem defect_eq_fieldDefect (s : ℝ) (q q' : ℕ) :
    defect s q q' = fieldDefect theta s q q' := rfl

/-- The defect is symmetric in its resolutions — inherited from the
field defect. -/
theorem defect_comm (s : ℝ) (q q' : ℕ) : defect s q q' = defect s q' q :=
  fieldDefect_comm theta s q q'

/-- **The defect vanishes on chains**: along a divisibility relation
`q ∣ q′` the pair `{gcd, lcm}` collapses to `{q, q′}` and the
four-term combination cancels identically — no positivity of `s`
needed. Inherited from the field defect. -/
theorem defect_eq_zero_of_dvd (s : ℝ) {q q' : ℕ} (hdvd : q ∣ q') :
    defect s q q' = 0 :=
  fieldDefect_eq_zero_of_dvd theta s hdvd

/-- The diagonal is a chain: `D_s(q, q) = 0`. -/
theorem defect_self (s : ℝ) (q : ℕ) : defect s q q = 0 :=
  defect_eq_zero_of_dvd s dvd_rfl

end Theaetetus
