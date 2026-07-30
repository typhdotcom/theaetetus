import Theaetetus.Diagonal
import Theaetetus.LogConvexity

/-! # The strict rectangle inequality for diagonal forms

The Boltzmann sum of
a positive diagonal form factors over its axes (`diagTheta`), so
log-partition functions add and strict convexity adds with them:
every positive diagonal form of rank `r ≥ 1` satisfies the strict
rectangle inequality

    Z(a²t)·Z(b²t) < Z(t)·Z((ab)²t)    (t > 0, a > 1, b > 1)

(`diagTheta_rect_strict`) and its midpoint case
(`diagTheta_sq_lt`) — the rank-one strict rectangle
(`theta_rect_strict`) lifted axis-by-axis, exactly as
`Theaetetus.Diagonal` lifts the sign. For the curvature
reconnaissance this pins the search space: no positive
diagonal form can be a counterexample, so the sweep starts at
non-orthogonal Gram matrices. The stronger reduction — any
counterexample yields an orthogonally *indecomposable* one —
awaits a formal orthogonal sum of lattice actions; the diagonal
case is what is closed here. -/

namespace Theaetetus

variable {r : ℕ} {c : Fin r → ℝ}

/-- **The strict rectangle inequality for positive diagonal
forms, every rank**: the
strict rectangle inequality for the factored Boltzmann sum — each
axis contributes a strict rank-one rectangle at scale `cᵢ·t`, and
the product over a nonempty axis set keeps the strictness. -/
theorem diagTheta_rect_strict (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    {t a b : ℝ} (ht : 0 < t) (ha : 1 < a) (hb : 1 < b) :
    diagTheta c (a ^ 2 * t) * diagTheta c (b ^ 2 * t)
      < diagTheta c t * diagTheta c ((a * b) ^ 2 * t) := by
  have ha0 : (0 : ℝ) < a := lt_trans one_pos ha
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  unfold diagTheta
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod_of_nonempty (fun i _ => ?_) (fun i _ => ?_)
    Finset.univ_nonempty
  · have hci := hc i
    exact mul_pos (theta_pos _ (by positivity)) (theta_pos _ (by positivity))
  · have hci := hc i
    have h := theta_rect_strict (mul_pos hci ht) ha hb
    rw [show a ^ 2 * (c i * t) = c i * (a ^ 2 * t) from by ring,
      show b ^ 2 * (c i * t) = c i * (b ^ 2 * t) from by ring,
      show (a * b) ^ 2 * (c i * t) = c i * ((a * b) ^ 2 * t) from by ring]
      at h
    exact h

/-- **The strict midpoint inequality for diagonal forms**: the
equal-leg case `Z(a²t)² < Z(t)·Z(a⁴t)` at every rank `r ≥ 1`,
every scale, every ratio `a > 1`. -/
theorem diagTheta_sq_lt (hr : r ≠ 0) (hc : ∀ i, 0 < c i)
    {t a : ℝ} (ht : 0 < t) (ha : 1 < a) :
    diagTheta c (a ^ 2 * t) ^ 2 < diagTheta c t * diagTheta c (a ^ 4 * t) := by
  have h := diagTheta_rect_strict hr hc ht ha ha
  rw [show (a * a) ^ 2 * t = a ^ 4 * t from by ring] at h
  nlinarith [h]

end Theaetetus
