-- ported from Meno/HarmonicForm.lean
import Theaetetus.QuadraticAction

/-! # Harmonic Gram Data: variational origin of a quadratic action

A `HarmonicGramData V` packages the analytic content the Hodge harmonic
construction supplies to a finite graph on `V`:

* the intended first Betti number `r`,
* a symmetric positive-definite Gram form on `Fin r → ℝ`.

Summability of `exp(-kᵀ Q k)` on the integer lattice is **derived**
from positive-definiteness (`HarmonicGramData.summable`) —
never stored.

The Gram form is the data from which a `QuadraticAction` is built.
**The structure carries no variational field**: the identity "energy
k = least cochain energy at periods k" is proved *outside* the
structure — generically
for cycle-built data by `HarmonicGramData.ofCycles_energy_isLeast`
(`Theaetetus/Periods.lean`).

This file also hosts the generic Gram-level sector algebra: energy
positivity for nonzero sectors, the interaction bilinear form, and
polarization. These are pure
matrix-level facts, independent of any particular graph. -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u

/-- Abstract harmonic Gram data on a vertex type `V`.

`r` is the intended first Betti number; `gram` is the Gram form of a
harmonic 1-cochain basis. Summability of the Boltzmann weight is
derived (`HarmonicGramData.summable`), never stored.

This structure is positive-definite matrix
data and nothing more — it does not carry a variational field, and
nothing here ties `gram` to a graph or to a minimization. The
variational identity lives at the graph level
(`IncidenceGraph.harmonicEnergy_isLeast`, `Theaetetus/Carrier.lean`). -/
structure HarmonicGramData (V : Type u) where
  r : ℕ
  gram : Matrix (Fin r) (Fin r) ℝ
  gram_posDef : gram.PosDef

namespace HarmonicGramData

variable {V : Type u} (H : HarmonicGramData V)

/-- Symmetry of the Gram form — a theorem of positive-definiteness
over ℝ. -/
theorem gram_symm : H.gram.IsSymm := H.gram_posDef.isSymm

/-- Summability of the Boltzmann weight — a theorem of the
positive-definite Gram. -/
theorem summable : Summable (fun k : Fin H.r → ℤ =>
    Real.exp (-(∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)))) :=
  summable_exp_neg_quadForm H.gram_posDef

/-- The Gram-form energy `kᵀ Q k` on integer windings. For instances
built from a graph, a separate per-instance theorem identifies this
with the harmonic energy minimum within the winding class; the
structure itself does not enforce it. -/
noncomputable def energy (k : Fin H.r → ℤ) : ℝ :=
  ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)

/-- The `QuadraticAction` produced by the harmonic Gram data. -/
noncomputable def toQuadraticAction : QuadraticAction H.r where
  Q := H.gram
  Q_posDef := H.gram_posDef

theorem toQuadraticAction_Q : H.toQuadraticAction.Q = H.gram := rfl

theorem toQuadraticAction_energy (k : Fin H.r → ℤ) :
    H.toQuadraticAction.energy k = H.energy k := rfl

/-! ## Generic sector algebra -/

/-- Positive-definiteness gives every nonzero sector strictly positive
energy. (This is why "positive action" is a *theorem* about sectors,
never stored data.) -/
theorem energy_pos_of_ne_zero (k : Fin H.r → ℤ) (hk : k ≠ 0) :
    0 < H.energy k := by
  have hReal : (fun i => (k i : ℝ)) ≠ 0 := by
    intro h
    apply hk
    ext i
    have : (k i : ℝ) = 0 := congrFun h i
    exact_mod_cast this
  have hPos := H.gram_posDef.dotProduct_mulVec_pos (x := fun i => (k i : ℝ)) hReal
  have hStar : (star (fun i : Fin H.r => (k i : ℝ))) = fun i => (k i : ℝ) := by
    funext i; exact star_trivial _
  rw [hStar] at hPos
  show 0 < ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
  have hExpand : ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
      = (fun i => (k i : ℝ)) ⬝ᵥ H.gram.mulVec (fun i => (k i : ℝ)) := by
    show ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
      = ∑ i, (k i : ℝ) * ∑ j, H.gram i j * (k j : ℝ)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hExpand]; exact hPos

/-- The zero sector has zero energy. -/
theorem energy_zero : H.energy 0 = 0 := by
  show ∑ i, ∑ j, H.gram i j * ((0 : Fin H.r → ℤ) i : ℝ)
      * ((0 : Fin H.r → ℤ) j : ℝ) = 0
  simp

/-- Energy is even: the quadratic form ignores orientation. -/
theorem energy_neg (k : Fin H.r → ℤ) : H.energy (-k) = H.energy k := by
  show ∑ i, ∑ j, H.gram i j * ((-k) i : ℝ) * ((-k) j : ℝ)
    = ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast [Pi.neg_apply]
  ring

/-! ## Interaction algebra

Pure `HarmonicGramData` operations: the interaction bilinear form and
polarization. Graph-specific instances stay downstream. -/

/-- The Gram bilinear form (interaction) between two sectors. -/
noncomputable def interaction (a b : Fin H.r → ℤ) : ℝ :=
  ∑ i, ∑ j, H.gram i j * (a i : ℝ) * (b j : ℝ)

/-- Polarization: energy of a joint sector. -/
theorem energy_add (a b : Fin H.r → ℤ) :
    H.energy (a + b) = H.energy a + H.energy b + 2 * H.interaction a b := by
  have hswap : ∑ i, ∑ j, H.gram i j * (b i : ℝ) * (a j : ℝ)
      = ∑ i, ∑ j, H.gram i j * (a i : ℝ) * (b j : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show H.gram j i = H.gram i j from by
      calc H.gram j i = H.gramᵀ i j := rfl
        _ = H.gram i j := by rw [show H.gramᵀ = H.gram from H.gram_symm]]
    ring
  show ∑ i, ∑ j, H.gram i j * ((a + b) i : ℝ) * ((a + b) j : ℝ) = _
  calc ∑ i, ∑ j, H.gram i j * ((a + b) i : ℝ) * ((a + b) j : ℝ)
      = ∑ i, ∑ j, (H.gram i j * (a i : ℝ) * (a j : ℝ)
          + H.gram i j * (a i : ℝ) * (b j : ℝ)
          + (H.gram i j * (b i : ℝ) * (a j : ℝ)
          + H.gram i j * (b i : ℝ) * (b j : ℝ))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        push_cast [Pi.add_apply]
        ring
    _ = (∑ i, ∑ j, H.gram i j * (a i : ℝ) * (a j : ℝ))
        + (∑ i, ∑ j, H.gram i j * (a i : ℝ) * (b j : ℝ))
        + ((∑ i, ∑ j, H.gram i j * (b i : ℝ) * (a j : ℝ))
        + (∑ i, ∑ j, H.gram i j * (b i : ℝ) * (b j : ℝ))) := by
        simp only [Finset.sum_add_distrib]
    _ = H.energy a + H.energy b + 2 * H.interaction a b := by
        rw [hswap]
        show _ = (∑ i, ∑ j, H.gram i j * (a i : ℝ) * (a j : ℝ))
          + (∑ i, ∑ j, H.gram i j * (b i : ℝ) * (b j : ℝ))
          + 2 * ∑ i, ∑ j, H.gram i j * (a i : ℝ) * (b j : ℝ)
        ring

end HarmonicGramData

end Theaetetus
