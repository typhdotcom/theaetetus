import Theaetetus.FieldDefect
import Descent.Core.Field
import Descent.Core.Defect
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
specializes to partition fields. -/

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

end Theaetetus
