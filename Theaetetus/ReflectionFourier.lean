import Theaetetus.CorrelationEquality

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

What the transformed criterion leaves open is the
cancellation question. Every coefficient is strictly positive, but
the sine products are not of one sign, so vanishing is not settled
termwise: it is a question of how the characters cancel across the
dual lattice. Deciding it for coprime `a, b > 1` in positive rank
is the remaining rigidity step. -/

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

end Theaetetus
