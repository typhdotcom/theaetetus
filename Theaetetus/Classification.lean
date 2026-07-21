import Theaetetus.CrossRatio
import Theaetetus.Submodular

/-! # Toward the classification: the kernel on the first carrier

**Q3, first slice.** Call a carrier **Euler-factorizable** when its
defect matrix vanishes identically — equivalently, when its residue
complexity is a valuation on the divisibility lattice, the algebraic
shadow of an Euler product. Q3 conjectures only rank zero qualifies.

On the first nontrivial carrier the question is now settled
completely: through the carrier bridge
(`cycle3_towerDefect_eq_defect`) and Q1 at rank one
(`defect_neg_of_incomparable`, `defect_eq_zero_iff`), the tower
defect of `C₃` is strictly negative at **every** incomparable pair
(`cycle3_towerDefect_neg_of_incomparable`), and its kernel is
**exactly** the chain relation (`cycle3_towerDefect_eq_zero_iff`) —
the first complete kernel computation of a defect matrix at carrier
level. In particular `C₃` is as far from Euler-factorizable as a
carrier can be: the failure is witnessed everywhere off the chains. -/

namespace Theaetetus

/-- **The sign on `C₃`, everywhere** (Q1 at the first carrier,
closed): the tower defect of the smallest rank-one carrier is
strictly negative at every incomparable pair of resolutions. -/
theorem cycle3_towerDefect_neg_of_incomparable (q q' : ℕ) [NeZero q] [NeZero q']
    (hqq' : ¬q ∣ q') (hq'q : ¬q' ∣ q) :
    (cycleGraph 3 (by norm_num)).towerDefect q q' < 0 := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_neg_of_incomparable (by norm_num) hqq' hq'q

/-- **The kernel on `C₃`** (Q3 at the first carrier): the tower
defect vanishes exactly on chains — `C₃` is not Euler-factorizable,
and its defect matrix detects divisibility. -/
theorem cycle3_towerDefect_eq_zero_iff (q q' : ℕ) [NeZero q] [NeZero q'] :
    (cycleGraph 3 (by norm_num)).towerDefect q q' = 0 ↔ q ∣ q' ∨ q' ∣ q := by
  rw [cycle3_towerDefect_eq_defect]
  exact defect_eq_zero_iff (by norm_num)

end Theaetetus
