import Theaetetus.CorrelationEquality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # The Fourier form of the two-grid criterion

The two-grid reflection criterion is an identity between shifted
Gaussian masses. This module transforms it into an identity between
Fourier sums over the dual lattice, whose coefficients are
themselves Gaussian and strictly positive.

The bridge is `gramMass_eq_periodization`: the shifted mass at
coupling `α` is the periodized Gaussian of the rescaled form
`(α/π)·M` at the same shift, which is what the Poisson machinery
consumes. Its Fourier expansion is therefore available at every
shift, with dual weights `massFourierCoeff M α m` — strictly
positive (`massFourierCoeff_pos`) and summable
(`summable_massFourierCoeff`) — and in real form the expansion is a
cosine series over the dual lattice (`hasSum_massFourier_cos`).

Reflection is a sine condition. Subtracting the expansions at
`y + t` and `y − t` leaves the bilinear sine sum
(`hasSum_massFourier_sin`), so the mass is symmetric about `y`
under the displacement `t` exactly when

    ∑_m C_m · sin(2π⟨m, y⟩) · sin(2π⟨m, t⟩) = 0

(`gramMass_reflect_iff`). The criterion is exactly the family of
these conditions: its anchors are the parity-refined points of the
`b`-grid (`anchorShift`) and its displacements the half points of
the `a`-grid (`displaceShift`), giving
`twoGridReflection_iff_fourier`. The anchors are precisely the
`2b`-grid, the parity digit supplying the leading half
(`anchorShift_eq_residueShift`, `exists_anchorShift`).

One heuristic is settled here, and negatively. Each instance has
the form of a reflection, and abstract reflections compose into
translations — but these identities hold only on their own fibers.
Because the mass is `ℤ^d`-periodic, chaining two instances needs
the reflected point of one to be a sampled point of the other only
*modulo the lattice*; that is the widest closure available. Even
so, at coprime dilations it forces twice the composed displacement
to be an integer vector (`chain_displacement_int`), hence the two
outer points of the chain to be congruent modulo `ℤ^d`
(`chain_endpoints_int`). The composed equality of masses therefore
holds by periodicity alone, for every form and every coupling,
criterion or not (`gramMass_chain_eq`, through
`gramMass_int_shift`). The sampled fibers close only trivially; no
rigidity follows from composition.

What the transformed criterion leaves open is the cancellation
question. Every coefficient is strictly positive, but the sine
products are not of one sign, so vanishing is not settled termwise:
it is a question of how the characters cancel across the dual
lattice. The rest of this module puts that question in its exact
finite form.

The criterion is symmetric in the two dilations
(`twoGridReflection_comm`, through the symmetry of the defect), so a
coprime pair may be oriented with `a` odd; then `a` is coprime to
`2b` and the two grids fuse. The sample points are exactly the
points of the `2ba`-grid — anchor digit and displacement digit
compose into the joint index (`jointIndex`, bijectively by
`jointIndex_injective` and `jointIndex_surjective`) — and reflection
becomes multiplication of that index by a CRT involution, `1` modulo
`2b` and `−1` modulo `a` (`exists_crtInvolution`,
`crtInvolution_dvd`, `crtInvolution_sq`). The criterion is therefore
a dilation invariance of the sampled mass
(`twoGridReflection_iff_crt`), and for a nontrivial pair the
dilation is itself nontrivial (`crtInvolution_nontrivial`).

Finite Fourier transformation turns that into invariance of alias
sums. Grouping the dual lattice by residue classes modulo the joint
denominator gives the alias weights `aliasSum`, each strictly
positive (`aliasSum_pos`), and at every grid point the mass is the
alias-weighted sum of the grid characters (`hasSum_aliasSum`,
`gramMass_eq_sum_aliasSum`). Distinct dual classes carry distinct
characters (`gridChar_injective`), so the characters are linearly
independent and the criterion is exactly

    A_ν = A_{Uν}   for every dual class ν

(`twoGridReflection_iff_alias`). Positivity does not finish the
argument: the condition equates positive alias sums; it does not
force any of them to vanish.

At rank one the invariance already fails
(`not_twoGridReflection_rankOne`, and in the two transformed forms
`exists_not_crt_invariant_rankOne` and `exists_aliasSum_ne_rankOne`),
because the strict rank-one sign theorem makes the defect of an
incomparable pair negative. The open rigidity statement is that the
failure persists in every positive rank.

The transform is canonical, and that is also its limit. The alias
sums are not merely positive aggregates: up to a single positive
prefactor each one is a shifted Gaussian mass of the *inverse* Gram
at the reflected coupling, evaluated at the grid point of its class
(`massFourierCoeff_eq`, `aliasSum_eq_dual`). At the criterion's own
coupling the reflected one is `2π²/s`, which is exactly the
coupling the criterion for `M⁻¹` at the reflected scale
`π²/(a²b²s)` uses — so invariance of the alias sums *is* that dual
criterion (`aliasSum_invariant_iff_dual`), and the criterion was
already self-dual at the defect level (`twoGridReflection_dual`,
through `gramDefect_dual_coprime`). The Fourier route therefore
closes a loop: it rediscovers duality rather than supplying a new
strictness mechanism. Positivity of the alias sums equates them
across the involution and stops there; a proof of the rigidity
statement must break the symmetry this transform preserves. -/

namespace Theaetetus

open Matrix UnitAddTorus

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-! ## The Fourier expansion of the shifted mass -/

/-- The Fourier coefficient of the shifted Gaussian mass at coupling
`α`: the Gaussian Fourier coefficient of the rescaled Gram form. -/
noncomputable def massFourierCoeff (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    (m : Fin d → ℤ) : ℝ :=
  gaussFourierCoeff ((α / Real.pi) • M) m

/-- Every Fourier coefficient of the shifted mass is strictly
positive: the dual weights are themselves Gaussian. -/
theorem massFourierCoeff_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (m : Fin d → ℤ) : 0 < massFourierCoeff M α m :=
  gaussFourierCoeff_pos (posDef_smul' hM (div_pos hα Real.pi_pos)) m

theorem summable_massFourierCoeff (hM : M.PosDef) {α : ℝ} (hα : 0 < α) :
    Summable (massFourierCoeff M α) :=
  summable_gaussFourierCoeff (posDef_smul' hM (div_pos hα Real.pi_pos))

/-- The pairing of a dual vector with a shift. -/
def dualPairing (m : Fin d → ℤ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (m i : ℝ) * x i

theorem dualPairing_add (m : Fin d → ℤ) (x y : Fin d → ℝ) :
    dualPairing m (x + y) = dualPairing m x + dualPairing m y := by
  unfold dualPairing
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    show (m i : ℝ) * (x i + y i) = _
    ring

theorem dualPairing_sub (m : Fin d → ℤ) (x y : Fin d → ℝ) :
    dualPairing m (x - y) = dualPairing m x - dualPairing m y := by
  unfold dualPairing
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    show (m i : ℝ) * (x i - y i) = _
    ring

/-- The torus character at a shift is the exponential of its
pairing. -/
theorem mFourier_torusMk (m : Fin d → ℤ) (x : Fin d → ℝ) :
    mFourier m (torusMk x)
      = Complex.exp (2 * Real.pi * Complex.I * (dualPairing m x : ℂ)) := by
  show (∏ i, fourier (m i) (torusMk x i)) = _
  have hterm : ∀ i : Fin d,
      fourier (m i) (torusMk x i)
        = Complex.exp (2 * Real.pi * Complex.I * ((m i : ℝ) * x i : ℝ)) := by
    intro i
    show fourier (m i) ((x i : ℝ) : UnitAddCircle) = _
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.exp_sum]
  congr 1
  rw [dualPairing, Complex.ofReal_sum, Finset.mul_sum]

/-- **The Fourier expansion of the shifted mass**: a positive
combination of the torus characters, summed over the dual lattice.
This is the engine form — the characters are the natural object for
finite orthogonality over the residue grids. -/
theorem hasSum_massFourier (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        ((massFourierCoeff M α m : ℝ) : ℂ) * mFourier m (torusMk x))
      ((gramMass M α x : ℝ) : ℂ) := by
  have hM' : ((α / Real.pi) • M).PosDef :=
    posDef_smul' hM (div_pos hα Real.pi_pos)
  have h := hasSum_gaussFourier_periodization hM' x
  rw [← gramMass_eq_periodization M α x] at h
  exact h

/-- The real form of the expansion, through the cosine. -/
theorem hasSum_massFourier_cos (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        massFourierCoeff M α m
          * Real.cos (2 * Real.pi * dualPairing m x))
      (gramMass M α x) := by
  have h := hasSum_massFourier hM hα x
  have hre : ∀ m : Fin d → ℤ,
      (((massFourierCoeff M α m : ℝ) : ℂ) * mFourier m (torusMk x)).re
        = massFourierCoeff M α m
            * Real.cos (2 * Real.pi * dualPairing m x) := by
    intro m
    rw [mFourier_torusMk, show (2 * (Real.pi : ℂ) * Complex.I
        * (dualPairing m x : ℂ))
        = ((2 * Real.pi * dualPairing m x : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simpa only [hre, Complex.ofReal_re] using Complex.hasSum_re h

/-! ## The reflection difference -/

/-- **The reflection difference**: the failure of the shifted mass
to be symmetric about `y` under the displacement `t` is the
sine-bilinear Fourier sum. -/
theorem hasSum_massFourier_sin (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (y t : Fin d → ℝ) :
    HasSum (fun m : Fin d → ℤ =>
        massFourierCoeff M α m
          * (Real.sin (2 * Real.pi * dualPairing m y)
              * Real.sin (2 * Real.pi * dualPairing m t)))
      ((gramMass M α (y - t) - gramMass M α (y + t)) / 2) := by
  have hplus := hasSum_massFourier_cos hM hα (y + t)
  have hminus := hasSum_massFourier_cos hM hα (y - t)
  have h := (hminus.sub hplus).div_const 2
  have hcos : ∀ u v : ℝ,
      Real.cos (2 * Real.pi * (u - v)) - Real.cos (2 * Real.pi * (u + v))
        = 2 * (Real.sin (2 * Real.pi * u) * Real.sin (2 * Real.pi * v)) := by
    intro u v
    rw [show 2 * Real.pi * (u - v)
        = 2 * Real.pi * u - 2 * Real.pi * v by ring,
      show 2 * Real.pi * (u + v)
        = 2 * Real.pi * u + 2 * Real.pi * v by ring,
      Real.cos_sub, Real.cos_add]
    ring
  refine h.congr_fun fun m => ?_
  rw [dualPairing_add, dualPairing_sub]
  linear_combination (-(massFourierCoeff M α m) / 2)
    * hcos (dualPairing m y) (dualPairing m t)

/-- **The reflection criterion, transformed**: the shifted mass is
symmetric about `y` under the displacement `t` exactly when the
sine-bilinear Fourier sum vanishes. -/
theorem gramMass_reflect_iff (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (y t : Fin d → ℝ) :
    gramMass M α (y + t) = gramMass M α (y - t)
      ↔ (∑' m : Fin d → ℤ, massFourierCoeff M α m
            * (Real.sin (2 * Real.pi * dualPairing m y)
                * Real.sin (2 * Real.pi * dualPairing m t))) = 0 := by
  rw [(hasSum_massFourier_sin hM hα y t).tsum_eq]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have := div_eq_zero_iff.mp h
    rcases this with h' | h'
    · linarith [sub_eq_zero.mp h']
    · norm_num at h'

/-! ## The criterion in Fourier form -/

/-- The anchor of a reflection instance: the parity-refined point of
the `b`-grid about which the criterion reflects. -/
noncomputable def anchorShift (b : ℕ) (r : Fin d → ZMod b)
    (e : Fin d → ZMod 2) : Fin d → ℝ :=
  (2 : ℝ)⁻¹ • (residueShift b r + fun i => ((e i).val : ℝ))

/-- The displacement of a reflection instance: a half point of the
`a`-grid. -/
noncomputable def displaceShift (a : ℕ) (c : Fin d → ZMod a) : Fin d → ℝ :=
  (2 : ℝ)⁻¹ • residueShift a c

theorem parityVector_residueShift_add (M : Matrix (Fin d) (Fin d) ℝ) (β : ℝ)
    {a b : ℕ} (r : Fin d → ZMod b) (c : Fin d → ZMod a)
    (e : Fin d → ZMod 2) :
    parityVector M β (residueShift b r + residueShift a c) e
      = gramMass M (2 * β) (anchorShift b r e + displaceShift a c) := by
  unfold parityVector anchorShift displaceShift
  congr 1
  funext i
  show (2 : ℝ)⁻¹ * (((b : ℝ)⁻¹ * ((r i).val : ℝ)
      + (a : ℝ)⁻¹ * ((c i).val : ℝ)) + ((e i).val : ℝ))
      = (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * ((r i).val : ℝ) + ((e i).val : ℝ))
        + (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * ((c i).val : ℝ))
  ring

theorem parityVector_residueShift_sub (M : Matrix (Fin d) (Fin d) ℝ) (β : ℝ)
    {a b : ℕ} (r : Fin d → ZMod b) (c : Fin d → ZMod a)
    (e : Fin d → ZMod 2) :
    parityVector M β (residueShift b r - residueShift a c) e
      = gramMass M (2 * β) (anchorShift b r e - displaceShift a c) := by
  unfold parityVector anchorShift displaceShift
  congr 1
  funext i
  show (2 : ℝ)⁻¹ * (((b : ℝ)⁻¹ * ((r i).val : ℝ)
      - (a : ℝ)⁻¹ * ((c i).val : ℝ)) + ((e i).val : ℝ))
      = (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * ((r i).val : ℝ) + ((e i).val : ℝ))
        - (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * ((c i).val : ℝ))
  ring

/-- **The two-grid criterion in Fourier form**: the criterion holds
exactly when, for every anchor of the parity-refined `b`-grid and
every displacement of the half `a`-grid, the sine-bilinear sum over
the dual lattice vanishes. Every coefficient in that sum is strictly
positive; the two sine factors carry the whole condition. -/
theorem twoGridReflection_iff_fourier (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    TwoGridReflection M s a b
      ↔ ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a) (e : Fin d → ZMod 2),
          (∑' m : Fin d → ℤ,
              massFourierCoeff M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) m
                * (Real.sin (2 * Real.pi
                      * dualPairing m (anchorShift b r e))
                    * Real.sin (2 * Real.pi
                      * dualPairing m (displaceShift a c)))) = 0 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hβ : (0 : ℝ) < 2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) := by positivity
  constructor
  · intro h r c e
    rw [← gramMass_reflect_iff hM hβ (anchorShift b r e) (displaceShift a c),
      ← parityVector_residueShift_add, ← parityVector_residueShift_sub]
    exact congrFun (h r c) e
  · intro h r c
    funext e
    rw [parityVector_residueShift_add, parityVector_residueShift_sub,
      gramMass_reflect_iff hM hβ]
    exact h r c e

/-! ## The sampled reflections do not compose -/

private theorem dvd_of_chain {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) (r r' : ZMod b) (e e' : ZMod 2)
    (c c' : ZMod a) (z₀ : ℤ)
    (h : (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * (r.val : ℝ) + (e.val : ℝ))
          - (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (c.val : ℝ))
        = (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * (r'.val : ℝ) + (e'.val : ℝ))
          + (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (c'.val : ℝ)) + (z₀ : ℝ)) :
    (a : ℤ) ∣ ((c.val : ℤ) + (c'.val : ℤ)) := by
  have haR : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    exact this.ne'
  have hbR : (b : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    exact this.ne'
  field_simp at h
  have keyZ : (b : ℤ) * (((c.val : ℤ)) + ((c'.val : ℤ)))
      = (a : ℤ) * ((((r.val : ℤ)) + (b : ℤ) * ((e.val : ℤ)))
          - (((r'.val : ℤ)) + (b : ℤ) * ((e'.val : ℤ)))
          - 2 * (b : ℤ) * z₀) := by
    have hR : (b : ℝ) * (((c.val : ℝ)) + ((c'.val : ℝ)))
        = (a : ℝ) * ((((r.val : ℝ)) + (b : ℝ) * ((e.val : ℝ)))
            - (((r'.val : ℝ)) + (b : ℝ) * ((e'.val : ℝ)))
            - 2 * (b : ℝ) * (z₀ : ℝ)) := by linarith
    exact_mod_cast hR
  exact (Nat.isCoprime_iff_coprime.mpr hco).dvd_of_dvd_mul_left ⟨_, keyZ⟩

/-- **The composed displacement is integral**: if the reflected
point of one instance is a sampled point of another *up to the
lattice* — the only closure the periodic mass can offer — then at
coprime dilations twice the composed displacement is an integer
vector. -/
theorem chain_displacement_int {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) {r r' : Fin d → ZMod b}
    {e e' : Fin d → ZMod 2} {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    ∃ z : Fin d → ℤ,
      (2 : ℝ) • (displaceShift a c + displaceShift a c')
        = fun i => ((z i : ℤ) : ℝ) := by
  have haR : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    exact this.ne'
  have hcoord : ∀ i : Fin d,
      (a : ℤ) ∣ ((((c i).val : ℤ)) + (((c' i).val : ℤ))) := by
    intro i
    refine dvd_of_chain ha hb hco (r i) (r' i) (e i) (e' i) (c i) (c' i)
      (z₀ i) ?_
    have hi := congrFun h i
    show (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * (((r i).val : ℝ)) + (((e i).val : ℝ)))
        - (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (((c i).val : ℝ)))
      = (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * (((r' i).val : ℝ)) + (((e' i).val : ℝ)))
        + (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (((c' i).val : ℝ))) + ((z₀ i : ℤ) : ℝ)
    exact hi
  choose z hz using hcoord
  refine ⟨z, ?_⟩
  funext i
  have hzR : (((c i).val : ℝ)) + (((c' i).val : ℝ))
      = (a : ℝ) * (z i : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (hz i)
  show (2 : ℝ) * ((2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (((c i).val : ℝ)))
      + (2 : ℝ)⁻¹ * ((a : ℝ)⁻¹ * (((c' i).val : ℝ)))) = (z i : ℝ)
  field_simp
  linarith

/-- **The endpoints of a chain differ by a lattice vector**: the two
outer points of a composed pair of instances are congruent modulo
`ℤ^d`. -/
theorem chain_endpoints_int {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hco : Nat.Coprime a b) {r r' : Fin d → ZMod b}
    {e e' : Fin d → ZMod 2} {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    ∃ z : Fin d → ℤ,
      anchorShift b r e + displaceShift a c
        = (anchorShift b r' e' - displaceShift a c')
            + fun i => ((z i : ℤ) : ℝ) := by
  obtain ⟨w, hw⟩ := chain_displacement_int ha hb hco h
  refine ⟨fun i => z₀ i + w i, ?_⟩
  funext i
  have hwi := congrFun hw i
  have hi := congrFun h i
  show (anchorShift b r e) i + (displaceShift a c) i
      = ((anchorShift b r' e') i - (displaceShift a c') i)
        + ((z₀ i + w i : ℤ) : ℝ)
  have hwi' : 2 * ((displaceShift a c) i + (displaceShift a c') i)
      = ((w i : ℤ) : ℝ) := hwi
  have hi' : (anchorShift b r e) i - (displaceShift a c) i
      = (anchorShift b r' e') i + (displaceShift a c') i
        + ((z₀ i : ℤ) : ℝ) := hi
  push_cast
  linarith

/-- **The chain gives nothing new**: the composed equality of masses
at the outer points holds by lattice periodicity alone, for every
positive-definite form and every coupling, whether or not the
criterion holds. Composing sampled reflections therefore yields no
rigidity. -/
theorem gramMass_chain_eq (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b)
    {r r' : Fin d → ZMod b} {e e' : Fin d → ZMod 2}
    {c c' : Fin d → ZMod a} {z₀ : Fin d → ℤ}
    (h : anchorShift b r e - displaceShift a c
        = anchorShift b r' e' + displaceShift a c'
            + fun i => ((z₀ i : ℤ) : ℝ)) :
    gramMass M α (anchorShift b r e + displaceShift a c)
      = gramMass M α (anchorShift b r' e' - displaceShift a c') := by
  obtain ⟨z, hz⟩ := chain_endpoints_int ha hb hco h
  rw [hz, gramMass_int_shift]

/-! ## The anchors are the refined grid -/

/-- **The parity grid refines the residue grid**: an anchor of the
criterion is exactly a point of the `2b`-grid, the parity digit
supplying the leading half. -/
theorem anchorShift_eq_residueShift (b : ℕ) [NeZero b]
    (r : Fin d → ZMod b) (e : Fin d → ZMod 2) :
    anchorShift b r e
      = residueShift (2 * b)
          (fun i => (((r i).val + b * (e i).val : ℕ) : ZMod (2 * b))) := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have : NeZero (2 * b) := ⟨by omega⟩
  funext i
  have hlt : (r i).val + b * (e i).val < 2 * b := by
    have h1 : (r i).val < b := ZMod.val_lt (r i)
    have h2 : (e i).val < 2 := ZMod.val_lt (e i)
    have h3 : b * (e i).val ≤ b * 1 := Nat.mul_le_mul_left b (by omega)
    omega
  have hval : ((((r i).val + b * (e i).val : ℕ) : ZMod (2 * b))).val
      = (r i).val + b * (e i).val := ZMod.val_natCast_of_lt hlt
  have hbR : (b : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    exact this.ne'
  show (2 : ℝ)⁻¹ * ((b : ℝ)⁻¹ * (((r i).val : ℝ)) + (((e i).val : ℝ)))
      = ((2 * b : ℕ) : ℝ)⁻¹
          * (((((r i).val + b * (e i).val : ℕ) : ZMod (2 * b))).val : ℝ)
  rw [hval]
  push_cast
  field_simp

/-- Every point of the `2b`-grid is an anchor: the residue digit and
the parity digit exhaust it. -/
theorem exists_anchorShift (b : ℕ) [NeZero b] (k : Fin d → ZMod (2 * b)) :
    ∃ (r : Fin d → ZMod b) (e : Fin d → ZMod 2),
      anchorShift b r e = residueShift (2 * b) k := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have : NeZero (2 * b) := ⟨by omega⟩
  refine ⟨fun i => (((k i).val % b : ℕ) : ZMod b),
    fun i => (((k i).val / b : ℕ) : ZMod 2), ?_⟩
  rw [anchorShift_eq_residueShift]
  congr 1
  funext i
  have hklt : (k i).val < 2 * b := ZMod.val_lt (k i)
  have h1 : ((((k i).val % b : ℕ) : ZMod b)).val = (k i).val % b :=
    ZMod.val_natCast_of_lt (Nat.mod_lt _ hb)
  have h2 : ((((k i).val / b : ℕ) : ZMod 2)).val = (k i).val / b :=
    ZMod.val_natCast_of_lt (Nat.div_lt_of_lt_mul (by omega))
  rw [h1, h2, Nat.mod_add_div, ZMod.natCast_val, ZMod.cast_id]

/-! ## The joint sample grid -/

/-- Grid points with congruent numerators carry the same mass: the
Gaussian mass is invariant under integer translation, so a numerator
matters only modulo its denominator. -/
theorem gramMass_residueShift_of_intCast (M : Matrix (Fin d) (Fin d) ℝ)
    (α : ℝ) {L : ℕ} [NeZero L] (n : Fin d → ZMod L) (w : Fin d → ℤ)
    (h : ∀ i, n i = ((w i : ℤ) : ZMod L)) :
    gramMass M α (residueShift L n)
      = gramMass M α (fun i => (L : ℝ)⁻¹ * (w i : ℝ)) := by
  have hL : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hdvd : ∀ i, (L : ℤ) ∣ (((n i).val : ℤ) - w i) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, h i, sub_self]
  choose z hz using hdvd
  have hshift : residueShift L n
      = (fun i => (L : ℝ)⁻¹ * (w i : ℝ)) + fun i => ((z i : ℤ) : ℝ) := by
    funext i
    have hzi : (((n i).val : ℤ) : ℝ) = (w i : ℝ) + (L : ℝ) * (z i : ℝ) := by
      have hzr := congrArg (fun t : ℤ => (t : ℝ)) (hz i)
      push_cast at hzr ⊢
      linarith
    show (L : ℝ)⁻¹ * (((n i).val : ℕ) : ℝ)
      = (L : ℝ)⁻¹ * (w i : ℝ) + ((z i : ℤ) : ℝ)
    have hcast : (((n i).val : ℕ) : ℝ) = (((n i).val : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hcast, hzi]
    field_simp
  rw [hshift, gramMass_int_shift]

/-- The joint index of an anchor digit modulo `2b` and a displacement
digit modulo `a`: the numerator of the sample point over the common
denominator `2ba`. -/
def jointIndex (a b : ℕ) (k : ZMod (2 * b)) (c : ZMod a) :
    ZMod (2 * b * a) :=
  ((a * k.val + b * c.val : ℕ) : ZMod (2 * b * a))

/-- **A CRT involution** for the pair `(2b, a)`: an integer that is
`1` modulo `2b` and `−1` modulo `a`. It exists when the two moduli
are coprime — which is what orienting the coprime pair with `a` odd
secures. -/
theorem exists_crtInvolution {a b : ℕ} (hco : Nat.Coprime (2 * b) a) :
    ∃ U : ℤ, (2 * (b : ℤ)) ∣ U - 1 ∧ (a : ℤ) ∣ U + 1 := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hco
  refine ⟨1 - 4 * (b : ℤ) * x, ⟨-2 * x, by ring⟩, ⟨2 * y, ?_⟩⟩
  push_cast at hxy
  linarith

/-- The involution squares to the identity modulo the joint
denominator. -/
theorem crtInvolution_sq {a b : ℕ} {U : ℤ} (h1 : (2 * (b : ℤ)) ∣ U - 1)
    (h2 : (a : ℤ) ∣ U + 1) :
    (2 * (b : ℤ) * (a : ℤ)) ∣ U ^ 2 - 1 := by
  obtain ⟨w, hw⟩ := h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨w * v, by linear_combination (U + 1) * hw + (2 * (b : ℤ) * w) * hv⟩

private theorem dvd_two_b {a b : ℕ} : 2 * b ∣ 2 * b * a := Dvd.intro a rfl

private theorem dvd_a {a b : ℕ} : a ∣ 2 * b * a := Dvd.intro_left (2 * b) rfl

theorem jointIndex_cast_a {a b : ℕ} [NeZero a] (k : ZMod (2 * b))
    (c : ZMod a) :
    ZMod.castHom dvd_a (ZMod a) (jointIndex a b k c) = (b : ZMod a) * c := by
  rw [jointIndex, map_natCast]
  push_cast
  rw [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_val c,
    ZMod.cast_id]

theorem jointIndex_cast_two_b {a b : ℕ} [NeZero b] (k : ZMod (2 * b))
    (c : ZMod a) :
    ZMod.castHom dvd_two_b (ZMod (2 * b)) (jointIndex a b k c)
      = (a : ZMod (2 * b)) * k
        + (b : ZMod (2 * b)) * ((c.val : ℕ) : ZMod (2 * b)) := by
  have hb2 : NeZero (2 * b) := ⟨by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    omega⟩
  rw [jointIndex, map_natCast]
  push_cast
  rw [ZMod.natCast_val k, ZMod.cast_id]

theorem jointIndex_injective {a b : ℕ} [NeZero a] [NeZero b]
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) :
    Function.Injective
      (fun p : ZMod (2 * b) × ZMod a => jointIndex a b p.1 p.2) := by
  have hbunit : IsUnit (b : ZMod a) :=
    (ZMod.isUnit_iff_coprime b a).mpr (Nat.Coprime.symm hab)
  have haunit : IsUnit (a : ZMod (2 * b)) :=
    (ZMod.isUnit_iff_coprime a (2 * b)).mpr (Nat.Coprime.symm hco)
  rintro ⟨k, c⟩ ⟨k', c'⟩ h
  simp only at h
  have hc : c = c' := by
    have := congrArg (ZMod.castHom dvd_a (ZMod a)) h
    rw [jointIndex_cast_a, jointIndex_cast_a] at this
    exact hbunit.mul_left_cancel this
  subst hc
  have hk : k = k' := by
    have := congrArg (ZMod.castHom dvd_two_b (ZMod (2 * b))) h
    rw [jointIndex_cast_two_b, jointIndex_cast_two_b] at this
    exact haunit.mul_left_cancel (by linear_combination this)
  subst hk
  rfl

theorem jointIndex_surjective {a b : ℕ} [NeZero a] [NeZero b]
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) :
    Function.Surjective
      (fun p : ZMod (2 * b) × ZMod a => jointIndex a b p.1 p.2) := by
  have : NeZero (2 * b) := ⟨by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    omega⟩
  have : NeZero (2 * b * a) := ⟨by
    have h1 : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    have h2 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    positivity⟩
  have hcard : Fintype.card (ZMod (2 * b) × ZMod a)
      = Fintype.card (ZMod (2 * b * a)) := by
    rw [Fintype.card_prod, ZMod.card, ZMod.card, ZMod.card]
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨jointIndex_injective hco hab, hcard⟩ |>.2

/-- **The involution reflects the joint index**: multiplying the
numerator of a sample point by an integer that is `1` modulo `2b`
and `−1` modulo `a` negates its displacement digit and fixes its
anchor digit — modulo the joint denominator. Oddness of `a` is what
makes the second congruence carry the factor `2`. -/
theorem crtInvolution_dvd {a b : ℕ} (hodd : ¬ 2 ∣ a) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) (k c : ℤ) :
    ((2 * b * a : ℕ) : ℤ)
      ∣ U * ((a : ℤ) * k + (b : ℤ) * c) - ((a : ℤ) * k - (b : ℤ) * c) := by
  obtain ⟨w, hw⟩ := h1
  obtain ⟨v, hv⟩ := h2
  have hev : Even ((a : ℤ) * v) := ⟨1 + (b : ℤ) * w, by linarith⟩
  have hna : ¬ Even ((a : ℤ)) := by
    rw [Int.even_coe_nat]
    exact fun hE => hodd hE.two_dvd
  obtain ⟨v', hv'⟩ := (Int.even_mul.mp hev).resolve_left hna
  refine ⟨w * k + v' * c, ?_⟩
  push_cast
  linear_combination ((a : ℤ) * k) * hw + ((b : ℤ) * c) * hv
    + ((b : ℤ) * c * (a : ℤ)) * hv'

/-! ## The criterion on the joint grid -/

/-- The criterion, unfolded at the anchors and displacements. -/
theorem twoGridReflection_iff_anchor (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (a b : ℕ) :
    TwoGridReflection M s a b
      ↔ ∀ (r : Fin d → ZMod b) (c : Fin d → ZMod a) (e : Fin d → ZMod 2),
          gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
              (anchorShift b r e + displaceShift a c)
            = gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
                (anchorShift b r e - displaceShift a c) := by
  constructor
  · intro h r c e
    rw [← parityVector_residueShift_add, ← parityVector_residueShift_sub]
    exact congrFun (h r c) e
  · intro h r c
    funext e
    rw [parityVector_residueShift_add, parityVector_residueShift_sub]
    exact h r c e

/-- The criterion on the anchor grid: the anchors are the whole
`2b`-grid. -/
theorem twoGridReflection_iff_grid (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (a : ℕ) {b : ℕ} [NeZero b] :
    TwoGridReflection M s a b
      ↔ ∀ (k : Fin d → ZMod (2 * b)) (c : Fin d → ZMod a),
          gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
              (residueShift (2 * b) k + displaceShift a c)
            = gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
                (residueShift (2 * b) k - displaceShift a c) := by
  rw [twoGridReflection_iff_anchor]
  constructor
  · intro h k c
    obtain ⟨r, e, hre⟩ := exists_anchorShift b k
    rw [← hre]
    exact h r c e
  · intro h r c e
    rw [anchorShift_eq_residueShift]
    exact h _ c

private theorem neZero_joint {a b : ℕ} [NeZero a] [NeZero b] :
    NeZero (2 * b * a) := by
  have h1 : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have h2 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  exact ⟨by positivity⟩

/-- **The sample point is a joint grid point**: anchor plus
displacement is the grid point of the joint index. -/
theorem gramMass_grid_add (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) {a b : ℕ}
    [NeZero a] [NeZero b] (k : Fin d → ZMod (2 * b)) (c : Fin d → ZMod a) :
    gramMass M α (residueShift (2 * b) k + displaceShift a c)
      = gramMass M α
          (residueShift (2 * b * a)
            (fun i => jointIndex a b (k i) (c i))) := by
  have : NeZero (2 * b * a) := neZero_joint
  have hcast : ∀ i : Fin d, jointIndex a b (k i) (c i)
      = ((((a : ℤ) * ((k i).val : ℤ) + (b : ℤ) * ((c i).val : ℤ)) : ℤ)
          : ZMod (2 * b * a)) := by
    intro i
    rw [jointIndex]
    push_cast
    ring
  rw [gramMass_residueShift_of_intCast M α _
    (fun i => (a : ℤ) * ((k i).val : ℤ) + (b : ℤ) * ((c i).val : ℤ)) hcast]
  congr 1
  funext i
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact_mod_cast this
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    exact_mod_cast this
  show ((2 * b : ℕ) : ℝ)⁻¹ * (((k i).val : ℕ) : ℝ)
      + (2 : ℝ)⁻¹ * (((a : ℕ) : ℝ)⁻¹ * (((c i).val : ℕ) : ℝ))
    = ((2 * b * a : ℕ) : ℝ)⁻¹
        * ((((a : ℤ) * ((k i).val : ℤ) + (b : ℤ) * ((c i).val : ℤ)) : ℤ) : ℝ)
  push_cast
  field_simp

/-- **The reflected sample point is the involution's grid point**:
anchor minus displacement is the grid point of the joint index
multiplied by the CRT involution. -/
theorem gramMass_grid_sub (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) {a b : ℕ}
    [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1)
    (k : Fin d → ZMod (2 * b)) (c : Fin d → ZMod a) :
    gramMass M α (residueShift (2 * b) k - displaceShift a c)
      = gramMass M α
          (residueShift (2 * b * a)
            (fun i =>
              (U : ZMod (2 * b * a)) * jointIndex a b (k i) (c i))) := by
  have : NeZero (2 * b * a) := neZero_joint
  have hcast : ∀ i : Fin d,
      (U : ZMod (2 * b * a)) * jointIndex a b (k i) (c i)
      = ((((a : ℤ) * ((k i).val : ℤ) - (b : ℤ) * ((c i).val : ℤ)) : ℤ)
          : ZMod (2 * b * a)) := by
    intro i
    rw [jointIndex]
    have hd := crtInvolution_dvd hodd h1 h2 ((k i).val : ℤ) ((c i).val : ℤ)
    have hz : (((U * ((a : ℤ) * ((k i).val : ℤ) + (b : ℤ) * ((c i).val : ℤ))
        - ((a : ℤ) * ((k i).val : ℤ) - (b : ℤ) * ((c i).val : ℤ))) : ℤ)
        : ZMod (2 * b * a)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    push_cast at hz ⊢
    linear_combination hz
  rw [gramMass_residueShift_of_intCast M α _
    (fun i => (a : ℤ) * ((k i).val : ℤ) - (b : ℤ) * ((c i).val : ℤ)) hcast]
  congr 1
  funext i
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact_mod_cast this
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    exact_mod_cast this
  show ((2 * b : ℕ) : ℝ)⁻¹ * (((k i).val : ℕ) : ℝ)
      - (2 : ℝ)⁻¹ * (((a : ℕ) : ℝ)⁻¹ * (((c i).val : ℕ) : ℝ))
    = ((2 * b * a : ℕ) : ℝ)⁻¹
        * ((((a : ℤ) * ((k i).val : ℤ) - (b : ℤ) * ((c i).val : ℤ)) : ℤ) : ℝ)
  push_cast
  field_simp

/-- **The criterion is a CRT dilation invariance**: with the coprime
pair oriented so that `a` is odd, the sample points of the criterion
are exactly the points of the `2ba`-grid, and reflection is
multiplication of the grid index by the CRT involution. -/
theorem twoGridReflection_iff_crt (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    {a b : ℕ} [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    TwoGridReflection M s a b
      ↔ ∀ n : Fin d → ZMod (2 * b * a),
          gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
              (residueShift (2 * b * a) n)
            = gramMass M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
                (residueShift (2 * b * a)
                  (fun i => (U : ZMod (2 * b * a)) * n i)) := by
  rw [twoGridReflection_iff_grid]
  constructor
  · intro h n
    choose p hp using fun i : Fin d => jointIndex_surjective hco hab (n i)
    have hk := h (fun i => (p i).1) (fun i => (p i).2)
    rw [gramMass_grid_add, gramMass_grid_sub _ _ hodd h1 h2] at hk
    simp only [hp] at hk
    exact hk
  · intro h k c
    rw [gramMass_grid_add, gramMass_grid_sub _ _ hodd h1 h2]
    exact h _

/-- **The involution is nontrivial**: for a nontrivial coprime pair
it is neither `1` nor `−1` modulo the joint denominator, so the
criterion asks for invariance under a genuine dilation of the
grid. -/
theorem crtInvolution_nontrivial {a b : ℕ} (hodd : ¬ 2 ∣ a) (ha : 1 < a)
    (hb : 1 < b) {U : ℤ} (h1 : (2 * (b : ℤ)) ∣ U - 1)
    (h2 : (a : ℤ) ∣ U + 1) :
    ¬ ((2 * b * a : ℕ) : ℤ) ∣ U - 1 ∧ ¬ ((2 * b * a : ℕ) : ℤ) ∣ U + 1 := by
  have haZ : (0 : ℤ) < (a : ℤ) := by
    exact_mod_cast Nat.lt_of_lt_of_le one_pos ha.le
  have hbZ : (0 : ℤ) < (b : ℤ) := by
    exact_mod_cast Nat.lt_of_lt_of_le one_pos hb.le
  constructor
  · intro hcon
    have hda : (a : ℤ) ∣ U - 1 :=
      dvd_trans ⟨2 * (b : ℤ), by push_cast; ring⟩ hcon
    have h2a : (a : ℤ) ∣ 2 := by
      have := dvd_sub h2 hda
      simpa using this
    have hd2 : (a : ℕ) ∣ 2 := by exact_mod_cast h2a
    have hale : a ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    have ha2 : a = 2 := by omega
    exact hodd (ha2 ▸ dvd_rfl)
  · intro hcon
    have hdb : (2 * (b : ℤ)) ∣ U + 1 :=
      dvd_trans ⟨(a : ℤ), by push_cast; ring⟩ hcon
    have h2b : (2 * (b : ℤ)) ∣ 2 := by
      have := dvd_sub hdb h1
      simpa using this
    have hble : (2 * (b : ℤ)) ≤ 2 := Int.le_of_dvd (by norm_num) h2b
    omega

/-! ## The rank-one calibration -/

private theorem posDef_one_one :
    (!![1] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    simp
  · have hx0 : x 0 ≠ 0 := by
      intro h
      exact hx (funext fun i => by fin_cases i; exact h)
    have hstar : star x = x := funext fun i => star_trivial _
    have hval : x ⬝ᵥ (!![1] : Matrix (Fin 1) (Fin 1) ℝ).mulVec x
        = x 0 * x 0 := by
      simp [Matrix.mulVec, dotProduct]
    rw [hstar, hval]
    exact mul_self_pos.mpr hx0

/-- **The criterion already fails at rank one**: the strict
rank-one sign theorem says the defect of an incomparable pair is
negative, so the two-grid reflection condition cannot hold there.
Whatever rigidity holds in higher rank must extend this. -/
theorem not_twoGridReflection_rankOne {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) (hab : ¬ a ∣ b)
    (hba : ¬ b ∣ a) :
    ¬ TwoGridReflection (!![1] : Matrix (Fin 1) (Fin 1) ℝ) s a b := by
  intro h
  have h0 := (gramDefect_eq_zero_iff_twoGridReflection posDef_one_one hs ha hb
    hco).mpr h
  rw [gramDefect_one_eq_defect] at h0
  exact absurd h0 (defect_neg_of_incomparable hs hab hba).ne

private theorem not_dvd_of_coprime {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hab : Nat.Coprime a b) : ¬ a ∣ b ∧ ¬ b ∣ a := by
  constructor
  · intro hd
    have hg : a ∣ Nat.gcd a b := Nat.dvd_gcd dvd_rfl hd
    rw [Nat.Coprime.gcd_eq_one hab] at hg
    have := Nat.le_of_dvd one_pos hg
    omega
  · intro hd
    have hg : b ∣ Nat.gcd a b := Nat.dvd_gcd hd dvd_rfl
    rw [Nat.Coprime.gcd_eq_one hab] at hg
    have := Nat.le_of_dvd one_pos hg
    omega

/-- The calibration in CRT form: at rank one the sampled Gaussian
mass is *not* invariant under the involution's dilation of the
grid. -/
theorem exists_not_crt_invariant_rankOne {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    ∃ n : Fin 1 → ZMod (2 * b * a),
      gramMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
            (residueShift (2 * b * a) n)
        ≠ gramMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
            (residueShift (2 * b * a)
              (fun i => (U : ZMod (2 * b * a)) * n i)) := by
  have : NeZero a := ⟨by omega⟩
  have : NeZero b := ⟨by omega⟩
  obtain ⟨hnd, hnd'⟩ := not_dvd_of_coprime ha hb hab
  by_contra hcon
  have hall : ∀ n : Fin 1 → ZMod (2 * b * a),
      gramMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
            (residueShift (2 * b * a) n)
        = gramMass (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
            (residueShift (2 * b * a)
              (fun i => (U : ZMod (2 * b * a)) * n i)) := by
    intro n
    by_contra hne
    exact hcon ⟨n, hne⟩
  exact not_twoGridReflection_rankOne hs (by omega) (by omega) hab hnd hnd'
    ((twoGridReflection_iff_crt _ s hodd hco hab h1 h2).mpr hall)

/-! ## Alias classes -/

/-- The pairing of a dual class with a grid index. -/
def gridPairing {L : ℕ} (ν n : Fin d → ZMod L) : ZMod L := ∑ i, ν i * n i

/-- The character of the joint grid at a dual class. -/
noncomputable def gridChar {L : ℕ} [NeZero L] (ν : Fin d → ZMod L) :
    AddChar (Fin d → ZMod L) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom
    (AddMonoidHom.mk' (gridPairing ν) fun x y => by
      simp only [gridPairing, Pi.add_apply, mul_add]
      rw [Finset.sum_add_distrib])

@[simp] theorem gridChar_apply {L : ℕ} [NeZero L] (ν n : Fin d → ZMod L) :
    gridChar ν n = ZMod.stdAddChar (gridPairing ν n) := rfl

/-- Distinct dual classes carry distinct characters. -/
theorem gridChar_injective {L : ℕ} [NeZero L] :
    Function.Injective (gridChar (d := d) (L := L)) := by
  intro ν ν' h
  funext i
  classical
  set u : Fin d → ZMod L := Pi.single i 1 with hu
  have hev := congrArg (fun ψ : AddChar (Fin d → ZMod L) ℂ => ψ u) h
  simp only [gridChar_apply] at hev
  have hsum : ∀ μ : Fin d → ZMod L, gridPairing μ u = μ i := by
    intro μ
    rw [gridPairing, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hj => by rw [hu, Pi.single_eq_of_ne hj, mul_zero])]
    rw [hu, Pi.single_eq_same, mul_one]
  rw [hsum, hsum] at hev
  exact ZMod.injective_stdAddChar hev

/-- The torus character at a grid point is the grid character of the
reduced dual vector. -/
theorem mFourier_residueShift {L : ℕ} [NeZero L] (m : Fin d → ℤ)
    (n : Fin d → ZMod L) :
    mFourier m (torusMk (residueShift L n))
      = gridChar (fun i => ((m i : ℤ) : ZMod L)) n := by
  have hL : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hpair : gridPairing (fun i => ((m i : ℤ) : ZMod L)) n
      = (((∑ i, m i * ((n i).val : ℤ)) : ℤ) : ZMod L) := by
    rw [gridPairing]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      rw [ZMod.natCast_val, ZMod.cast_id]
  rw [mFourier_torusMk, gridChar_apply, hpair, ZMod.stdAddChar_coe]
  congr 1
  have hdp : dualPairing m (residueShift L n)
      = (∑ i, (m i : ℝ) * (((n i).val : ℕ) : ℝ)) / (L : ℝ) := by
    rw [dualPairing, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      show (m i : ℝ) * ((L : ℝ)⁻¹ * (((n i).val : ℕ) : ℝ)) = _
      field_simp
  rw [hdp]
  push_cast
  field_simp

/-- **The alias sum** of a dual class: the total Fourier weight of
the dual vectors congruent to it modulo the joint denominator. -/
noncomputable def aliasSum (M : Matrix (Fin d) (Fin d) ℝ) (α : ℝ) (L : ℕ)
    (ν : Fin d → ZMod L) : ℝ :=
  ∑' m : {m : Fin d → ℤ // (fun i => ((m i : ℤ) : ZMod L)) = ν},
    massFourierCoeff M α (m : Fin d → ℤ)

theorem summable_aliasFiber (hM : M.PosDef) {α : ℝ} (hα : 0 < α) {L : ℕ}
    (ν : Fin d → ZMod L) :
    Summable
      (fun m : {m : Fin d → ℤ // (fun i => ((m i : ℤ) : ZMod L)) = ν} =>
        massFourierCoeff M α (m : Fin d → ℤ)) :=
  (summable_massFourierCoeff hM hα).subtype _

/-- Every alias sum is strictly positive: its class is nonempty and
every dual weight is positive. -/
theorem aliasSum_pos (hM : M.PosDef) {α : ℝ} (hα : 0 < α) {L : ℕ} [NeZero L]
    (ν : Fin d → ZMod L) : 0 < aliasSum M α L ν := by
  have hmem : (fun i => (((((ν i).val : ℕ) : ℤ) : ℤ)) : Fin d → ℤ)
      ∈ {m : Fin d → ℤ | (fun i => ((m i : ℤ) : ZMod L)) = ν} := by
    funext i
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  exact (summable_aliasFiber hM hα ν).tsum_pos
    (fun m => (massFourierCoeff_pos hM hα _).le) ⟨_, hmem⟩
    (massFourierCoeff_pos hM hα _)

/-- **The finite expansion at a grid point**: the mass at a grid
point is the alias-weighted sum of the grid characters. -/
theorem hasSum_aliasSum (hM : M.PosDef) {α : ℝ} (hα : 0 < α) {L : ℕ}
    [NeZero L] (n : Fin d → ZMod L) :
    HasSum (fun ν : Fin d → ZMod L =>
        ((aliasSum M α L ν : ℝ) : ℂ) * gridChar ν n)
      ((gramMass M α (residueShift L n) : ℝ) : ℂ) := by
  have hbase : HasSum (fun m : Fin d → ℤ =>
      ((massFourierCoeff M α m : ℝ) : ℂ)
        * gridChar (fun i => ((m i : ℤ) : ZMod L)) n)
      ((gramMass M α (residueShift L n) : ℝ) : ℂ) := by
    refine (hasSum_massFourier hM hα (residueShift L n)).congr_fun fun m => ?_
    rw [mFourier_residueShift]
  have hsig := ((Equiv.sigmaFiberEquiv
    (fun m : Fin d → ℤ => fun i => ((m i : ℤ) : ZMod L))).hasSum_iff
      (f := fun m : Fin d → ℤ =>
        ((massFourierCoeff M α m : ℝ) : ℂ)
          * gridChar (fun i => ((m i : ℤ) : ZMod L)) n)).mpr hbase
  refine hsig.sigma fun ν => ?_
  have hreal := ((summable_aliasFiber hM hα ν).hasSum.map
    (Complex.ofRealHom.toAddMonoidHom) Complex.continuous_ofReal).mul_right
      (gridChar ν n)
  refine hreal.congr_fun fun c => ?_
  show ((massFourierCoeff M α (c : Fin d → ℤ) : ℝ) : ℂ)
      * gridChar (fun i => (((c : Fin d → ℤ) i : ℤ) : ZMod L)) n
    = ((massFourierCoeff M α (c : Fin d → ℤ) : ℝ) : ℂ) * gridChar ν n
  rw [c.2]

/-- The expansion as a finite sum. -/
theorem gramMass_eq_sum_aliasSum (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    {L : ℕ} [NeZero L] (n : Fin d → ZMod L) :
    ((gramMass M α (residueShift L n) : ℝ) : ℂ)
      = ∑ ν : Fin d → ZMod L, ((aliasSum M α L ν : ℝ) : ℂ) * gridChar ν n :=
  (hasSum_aliasSum hM hα n).unique (hasSum_fintype _)

/-- **The alias-class equivalence**: the two-grid criterion holds
exactly when the alias sums are invariant under the CRT involution.
Every alias sum is positive, so the condition equates positive
Gaussian sums; it does not by itself make any of them vanish. -/
theorem twoGridReflection_iff_alias (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    TwoGridReflection M s a b
      ↔ ∀ ν : Fin d → ZMod (2 * b * a),
          aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
            = aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
                (fun i => (U : ZMod (2 * b * a)) * ν i) := by
  have hLz : NeZero (2 * b * a) := neZero_joint
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact_mod_cast this
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    exact_mod_cast this
  have hα : (0 : ℝ) < 2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) := by positivity
  set L := 2 * b * a with hLdef
  set α := 2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) with hαdef
  set u : ZMod L := (U : ZMod L) with hudef
  have hu2 : u * u = 1 := by
    have hsq := crtInvolution_sq h1 h2
    have hz : (((U ^ 2 - 1 : ℤ)) : ZMod L) = 0 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
      rw [hLdef]
      push_cast
      exact hsq
    push_cast at hz
    rw [hudef]
    linear_combination hz
  have hchar : ∀ ν n : Fin d → ZMod L,
      gridChar ν (fun i => u * n i) = gridChar (fun i => u * ν i) n := by
    intro ν n
    rw [gridChar_apply, gridChar_apply, gridPairing, gridPairing]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
  have hinv : ∀ ν : Fin d → ZMod L, (fun i => u * (u * ν i)) = ν := by
    intro ν
    funext i
    rw [← mul_assoc, hu2, one_mul]
  let e : (Fin d → ZMod L) ≃ (Fin d → ZMod L) :=
    { toFun := fun ν i => u * ν i
      invFun := fun ν i => u * ν i
      left_inv := fun ν => hinv ν
      right_inv := fun ν => hinv ν }
  rw [twoGridReflection_iff_crt M s hodd hco hab h1 h2]
  constructor
  · intro h ν
    have hpt : ∀ n : Fin d → ZMod L,
        ∑ μ : Fin d → ZMod L, ((aliasSum M α L μ : ℝ) : ℂ) * gridChar μ n
          = ∑ μ : Fin d → ZMod L,
              ((aliasSum M α L (fun i => u * μ i) : ℝ) : ℂ)
                * gridChar μ n := by
      intro n
      rw [← gramMass_eq_sum_aliasSum hM hα n, h n,
        gramMass_eq_sum_aliasSum hM hα (fun i => u * n i)]
      refine Fintype.sum_equiv e _ _ fun μ => ?_
      show ((aliasSum M α L μ : ℝ) : ℂ) * gridChar μ (fun i => u * n i)
        = ((aliasSum M α L (fun i => u * (u * μ i)) : ℝ) : ℂ)
            * gridChar (fun i => u * μ i) n
      rw [hchar, hinv]
    have hindep : LinearIndependent ℂ
        (fun ν : Fin d → ZMod L =>
          ((gridChar ν).toMonoidHom :
            Multiplicative (Fin d → ZMod L) → ℂ)) := by
      refine (linearIndependent_monoidHom
        (Multiplicative (Fin d → ZMod L)) ℂ).comp _ fun ν ν' hh => ?_
      exact gridChar_injective (AddChar.toMonoidHomEquiv.injective hh)
    have hfun : (∑ μ : Fin d → ZMod L, ((aliasSum M α L μ : ℝ) : ℂ) •
          ((gridChar μ).toMonoidHom : Multiplicative (Fin d → ZMod L) → ℂ))
        = ∑ μ : Fin d → ZMod L,
            ((aliasSum M α L (fun i => u * μ i) : ℝ) : ℂ) •
              ((gridChar μ).toMonoidHom :
                Multiplicative (Fin d → ZMod L) → ℂ) := by
      funext n
      simpa using hpt (Multiplicative.toAdd n)
    exact_mod_cast Fintype.linearIndependent_iffₛ.mp hindep _ _ hfun ν
  · intro h n
    have key : ((gramMass M α (residueShift L n) : ℝ) : ℂ)
        = ((gramMass M α (residueShift L (fun i => u * n i)) : ℝ) : ℂ) := by
      rw [gramMass_eq_sum_aliasSum hM hα n,
        gramMass_eq_sum_aliasSum hM hα (fun i => u * n i)]
      refine Fintype.sum_equiv e _ _ fun μ => ?_
      show ((aliasSum M α L μ : ℝ) : ℂ) * gridChar μ n
        = ((aliasSum M α L (fun i => u * μ i) : ℝ) : ℂ)
            * gridChar (fun i => u * μ i) (fun i => u * n i)
      rw [hchar, hinv, ← h μ]
    exact Complex.ofReal_inj.mp key

/-- **The rank-one calibration, on the alias classes**: at rank one
the alias sums are *not* invariant under the involution. Any
higher-rank rigidity theorem must extend this failure. -/
theorem exists_aliasSum_ne_rankOne {s : ℝ} (hs : 0 < s) {a b : ℕ}
    (ha : 1 < a) (hb : 1 < b) (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    ∃ ν : Fin 1 → ZMod (2 * b * a),
      aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
          (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
        ≠ aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
            (fun i => (U : ZMod (2 * b * a)) * ν i) := by
  have : NeZero a := ⟨by omega⟩
  have : NeZero b := ⟨by omega⟩
  obtain ⟨hnd, hnd'⟩ := not_dvd_of_coprime ha hb hab
  by_contra hcon
  have hall : ∀ ν : Fin 1 → ZMod (2 * b * a),
      aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
          (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
        = aliasSum (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
            (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
            (fun i => (U : ZMod (2 * b * a)) * ν i) := by
    intro ν
    by_contra hne
    exact hcon ⟨ν, hne⟩
  exact not_twoGridReflection_rankOne hs (by omega) (by omega) hab hnd hnd'
    ((twoGridReflection_iff_alias posDef_one_one hs hodd hco hab h1 h2).mpr
      hall)

/-! ## The alias sums are dual masses -/

/-- The dual weight in closed form: a Gaussian of the inverse Gram
at the reflected coupling, with a scale-and-determinant prefactor. -/
theorem massFourierCoeff_eq (hM : M.PosDef) {α : ℝ} (hα : 0 < α)
    (m : Fin d → ℤ) :
    massFourierCoeff M α m
      = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
        * Real.exp (-(Real.pi ^ 2 / α)
            * ∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) := by
  have hdet_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hMinv : ((α / Real.pi) • M)⁻¹ = (Real.pi / α) • M⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_nonsing_inv _ hdet_unit,
      show α / Real.pi * (Real.pi / α) = 1 from by
        field_simp, one_smul]
  unfold massFourierCoeff gaussFourierCoeff
  rw [Matrix.det_smul, Fintype.card_fin, hMinv]
  congr 1
  congr 1
  rw [neg_mul, neg_mul, neg_inj, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- The class of a dual residue is the `L`-dilate of the dual
lattice through its representative. -/
private def aliasEquiv {L : ℕ} [NeZero L] (ν : Fin d → ZMod L) :
    (Fin d → ℤ)
      ≃ {m : Fin d → ℤ // (fun i => ((m i : ℤ) : ZMod L)) = ν} where
  toFun k := ⟨fun i => (L : ℤ) * k i + ((ν i).val : ℤ), by
    funext i
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_val,
      ZMod.cast_id]⟩
  invFun m := fun i => ((m : Fin d → ℤ) i - ((ν i).val : ℤ)) / (L : ℤ)
  left_inv k := by
    funext i
    have hL : (L : ℤ) ≠ 0 := by
      have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      exact_mod_cast this.ne'
    show ((L : ℤ) * k i + ((ν i).val : ℤ) - ((ν i).val : ℤ)) / (L : ℤ) = k i
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ hL]
  right_inv m := by
    have hL : (L : ℤ) ≠ 0 := by
      have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      exact_mod_cast this.ne'
    refine Subtype.ext ?_
    funext i
    have hmem : (((m : Fin d → ℤ) i : ℤ) : ZMod L) = ν i := congrFun m.2 i
    have hdvd : (L : ℤ) ∣ ((m : Fin d → ℤ) i - ((ν i).val : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hmem, ZMod.natCast_val, ZMod.cast_id, sub_self]
    obtain ⟨t, ht⟩ := hdvd
    show (L : ℤ) * (((m : Fin d → ℤ) i - ((ν i).val : ℤ)) / (L : ℤ))
        + ((ν i).val : ℤ) = (m : Fin d → ℤ) i
    rw [ht, Int.mul_ediv_cancel_left _ hL]
    linarith

/-- **The alias sums are dual masses**: up to one positive
prefactor, the alias sum at a dual class is the shifted Gaussian
mass of the inverse Gram at the reflected coupling, evaluated at the
grid point of that class. -/
theorem aliasSum_eq_dual (hM : M.PosDef) {α : ℝ} (hα : 0 < α) {L : ℕ}
    [NeZero L] (ν : Fin d → ZMod L) :
    aliasSum M α L ν
      = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
        * gramMass M⁻¹ (Real.pi ^ 2 * (L : ℝ) ^ 2 / α)
            (residueShift L ν) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  rw [aliasSum, ← (aliasEquiv ν).tsum_eq
    (fun m : {m : Fin d → ℤ // (fun i => ((m i : ℤ) : ZMod L)) = ν} =>
      massFourierCoeff M α (m : Fin d → ℤ)), gramMass, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hquad : (∑ i, ∑ j, M⁻¹ i j
        * ((((L : ℤ) * k i + ((ν i).val : ℤ)) : ℤ) : ℝ)
        * ((((L : ℤ) * k j + ((ν j).val : ℤ)) : ℤ) : ℝ))
      = (L : ℝ) ^ 2 * ((residueShift L ν + fun i => ((k i : ℤ) : ℝ))
          ⬝ᵥ M⁻¹.mulVec (residueShift L ν + fun i => ((k i : ℤ) : ℝ))) := by
    rw [← quadForm_dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show M⁻¹ i j * ((((L : ℤ) * k i + ((ν i).val : ℤ)) : ℤ) : ℝ)
        * ((((L : ℤ) * k j + ((ν j).val : ℤ)) : ℤ) : ℝ)
      = (L : ℝ) ^ 2 * (M⁻¹ i j
          * ((L : ℝ)⁻¹ * (((ν i).val : ℕ) : ℝ) + ((k i : ℤ) : ℝ))
          * ((L : ℝ)⁻¹ * (((ν j).val : ℕ) : ℝ) + ((k j : ℤ) : ℝ)))
    push_cast
    field_simp
    ring
  rw [massFourierCoeff_eq hM hα]
  show ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
      * Real.exp (-(Real.pi ^ 2 / α)
          * ∑ i, ∑ j, M⁻¹ i j
              * ((((L : ℤ) * k i + ((ν i).val : ℤ)) : ℤ) : ℝ)
              * ((((L : ℤ) * k j + ((ν j).val : ℤ)) : ℤ) : ℝ))
    = ((α / Real.pi) ^ d * M.det)⁻¹ ^ ((1 : ℝ) / 2)
      * Real.exp (-(Real.pi ^ 2 * (L : ℝ) ^ 2 / α)
          * ((residueShift L ν + fun i => ((k i : ℤ) : ℝ))
              ⬝ᵥ M⁻¹.mulVec (residueShift L ν + fun i => ((k i : ℤ) : ℝ))))
  rw [hquad]
  congr 2
  field_simp

/-! ## The duality loop -/

/-- **The criterion is self-dual**: the two-grid reflection
condition for a Gram form at a scale is the same condition for the
dual Gram at the reflected scale. This is the defect duality
already known at coprime resolutions, read at the level of the
equality criterion. -/
theorem twoGridReflection_dual (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hco : Nat.Coprime a b) :
    TwoGridReflection M s a b
      ↔ TwoGridReflection M⁻¹
          (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)) a b := by
  have hinv : M⁻¹.PosDef := posDef_inv hM
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hs' : (0 : ℝ) < Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s) := by
    positivity
  rw [← gramDefect_eq_zero_iff_twoGridReflection hM hs ha hb hco,
    ← gramDefect_eq_zero_iff_twoGridReflection hinv hs' ha hb hco,
    gramDefect_dual_coprime hM hs ha hb hco]

/-- **The alias invariance is the dual criterion**: the finite
Fourier coordinates of the criterion are the dual masses, so
invariance of the alias sums under the involution is literally the
two-grid criterion for the dual Gram at the reflected scale. The
transform closes the duality loop; it introduces no mechanism
beyond it. -/
theorem aliasSum_invariant_iff_dual (hM : M.PosDef) {s : ℝ} (hs : 0 < s)
    {a b : ℕ} [NeZero a] [NeZero b] (hodd : ¬ 2 ∣ a)
    (hco : Nat.Coprime (2 * b) a) (hab : Nat.Coprime a b) {U : ℤ}
    (h1 : (2 * (b : ℤ)) ∣ U - 1) (h2 : (a : ℤ) ∣ U + 1) :
    (∀ ν : Fin d → ZMod (2 * b * a),
        aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a) ν
          = aliasSum M (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s))) (2 * b * a)
              (fun i => (U : ZMod (2 * b * a)) * ν i))
      ↔ TwoGridReflection M⁻¹
          (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)) a b := by
  have hLz : NeZero (2 * b * a) := neZero_joint
  have hinv : M⁻¹.PosDef := posDef_inv hM
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact_mod_cast this
  have hbR : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
    exact_mod_cast this
  have hα : (0 : ℝ) < 2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) := by positivity
  have hD : (0 : ℝ)
      < ((2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)) / Real.pi) ^ d * M.det)⁻¹
          ^ ((1 : ℝ) / 2) := by
    refine Real.rpow_pos_of_pos (inv_pos.mpr ?_) _
    have := hM.det_pos
    positivity
  have hcoup : Real.pi ^ 2 * ((2 * b * a : ℕ) : ℝ) ^ 2
        / (2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2 * s)))
      = 2 * ((a : ℝ) ^ 2 * ((b : ℝ) ^ 2
          * (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)))) := by
    push_cast
    field_simp
  rw [twoGridReflection_iff_crt M⁻¹
    (Real.pi ^ 2 / (((a : ℝ) * (b : ℝ)) ^ 2 * s)) hodd hco hab h1 h2]
  constructor
  · intro h n
    have hn := h n
    rw [aliasSum_eq_dual hM hα, aliasSum_eq_dual hM hα, hcoup] at hn
    exact mul_left_cancel₀ hD.ne' hn
  · intro h ν
    rw [aliasSum_eq_dual hM hα, aliasSum_eq_dual hM hα, hcoup]
    exact congrArg _ (h ν)

end Theaetetus
