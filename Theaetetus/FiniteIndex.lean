import Theaetetus.GramAsymptotics
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Int

/-! # The finite-index mass ratio

The Gaussian mass of a subgroup of the integer lattice is intrinsic
(`subMass`), but it is computed in a chart. A `ℤ`-basis of a
full-rank subgroup gives a chart matrix whose columns are the basis
vectors (`subChart`) and a pulled-back Gram form (`subGram`), and
the mass is the Boltzmann sum of that form
(`subMass_eq_gramTheta`).

Two facts make the chart usable. Its determinant is the index up to
sign (`natAbs_det_subChart`, through the Smith-normal-form count of
the quotient), so a finite-index subgroup has a nondegenerate chart
(`det_subChart_ne_zero`) and hence a positive-definite Gram form
(`subGram_posDef`), whose determinant is the squared index
(`det_subGram`).

The scale asymptotics then compare two subgroups: the rank
normalization cancels, so for a full-rank finite-index inclusion
`V ≤ U`

    ρ_s(U) / ρ_s(V) → [U : V]        as s → 0⁺

(`tendsto_subMass_ratio`), and in logarithmic form

    log ρ_s(U) − log ρ_s(V) → log [U : V]

(`tendsto_log_subMass_sub`) — the field gap that the order-three
recurrence consumes. Both hypotheses are carried explicitly: full
rank as a `ℤ`-basis indexed by the ambient rank, finite index as a
nonzero index. Nothing here is claimed across rank loss or infinite
index.

The direction is the one the Gaussian diamond exhibits: there the
doubled lattice sits inside the checkerboard with relative index
two, and the same limit is proved by duality
(`tendsto_defect3_diamond_index`). -/

namespace Theaetetus

open Filter Topology Matrix

variable {d : ℕ}

/-! ## The chart of a full-rank subgroup -/

/-- The Gaussian mass of a subgroup of the integer lattice at scale
`s`: the Boltzmann sum of the squared euclidean length over its
points. -/
noncomputable def subMass (s : ℝ) (H : AddSubgroup (Fin d → ℤ)) : ℝ :=
  ∑' v : H, Real.exp (-s * ∑ k, (((v : Fin d → ℤ) k : ℤ) : ℝ) ^ 2)

/-- The chart matrix of a basis of a subgroup: its columns are the
basis vectors, read in the ambient integer coordinates. -/
noncomputable def subChart {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun k i => (((b i : Fin d → ℤ) k : ℤ) : ℝ)

/-- The Gram chart of a basis of a subgroup: the pulled-back form,
the Gram matrix of the basis vectors under the ambient euclidean
structure. -/
noncomputable def subGram {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) : Matrix (Fin d) (Fin d) ℝ :=
  (subChart b)ᵀ * subChart b

theorem subGram_apply {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) (i j : Fin d) :
    subGram b i j
      = ∑ k, (((b i : Fin d → ℤ) k : ℤ) : ℝ)
          * (((b j : Fin d → ℤ) k : ℤ) : ℝ) := by
  simp only [subGram, Matrix.mul_apply, Matrix.transpose_apply, subChart,
    Matrix.of_apply]

/-- The chart determinant is the index, up to sign. -/
theorem natAbs_det_subChart {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) :
    ∃ n : ℤ, n.natAbs = H.index ∧ (subChart b).det = (n : ℝ) := by
  classical
  refine ⟨(Pi.basisFun ℤ (Fin d)).det (fun i => ((b i : Fin d → ℤ))), ?_, ?_⟩
  · exact (AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d)) H b).symm
  · rw [Module.Basis.det_apply]
    show (subChart b).det
      = (Int.castRingHom ℝ) (((Pi.basisFun ℤ (Fin d)).toMatrix
          fun i => ((b i : Fin d → ℤ))).det)
    rw [RingHom.map_det]
    congr 1

/-- **The chart is nondegenerate**: a finite-index subgroup has a
chart of nonzero determinant. -/
theorem det_subChart_ne_zero {H : AddSubgroup (Fin d → ℤ)}
    (hidx : H.index ≠ 0) (b : Module.Basis (Fin d) ℤ H) :
    (subChart b).det ≠ 0 := by
  obtain ⟨n, hn, hdet⟩ := natAbs_det_subChart b
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    exact hidx (by simpa using hn.symm)
  rw [hdet]
  exact_mod_cast hn0

/-- **The Gram chart is positive definite**: the pulled-back form of
a full-rank finite-index subgroup. -/
theorem subGram_posDef {H : AddSubgroup (Fin d → ℤ)} (hidx : H.index ≠ 0)
    (b : Module.Basis (Fin d) ℤ H) : (subGram b).PosDef := by
  have hdne := det_subChart_ne_zero hidx b
  have hherm : (subGram b).IsHermitian := by
    show (subGram b)ᴴ = subGram b
    rw [subGram, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun x hx => ?_⟩
  have hstar : star x = x := funext fun i => star_trivial _
  have hxB : (subChart b).mulVec x ≠ 0 := by
    intro h
    exact hx (Matrix.eq_zero_of_mulVec_eq_zero hdne h)
  have hval : x ⬝ᵥ (subGram b).mulVec x
      = (subChart b).mulVec x ⬝ᵥ (subChart b).mulVec x := by
    rw [subGram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [hstar, hval]
  obtain ⟨i, hi⟩ : ∃ i, (subChart b).mulVec x i ≠ 0 := by
    by_contra hcon
    exact hxB (funext fun i => by
      by_contra hne
      exact hcon ⟨i, hne⟩)
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr hi

/-- The determinant of the Gram chart is the squared index. -/
theorem det_subGram {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) :
    (subGram b).det = ((H.index : ℝ)) ^ 2 := by
  obtain ⟨n, hn, hdet⟩ := natAbs_det_subChart b
  rw [subGram, Matrix.det_mul, Matrix.det_transpose, hdet]
  have hidxR : ((H.index : ℝ)) = |(n : ℝ)| := by
    rw [← hn]
    calc ((n.natAbs : ℕ) : ℝ)
        = (((n.natAbs : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
      _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(n : ℝ)| := Int.cast_abs
  rw [hidxR, sq_abs]
  ring

/-! ## The chart formula for the mass -/

private theorem coe_equivFun_symm {H : AddSubgroup (Fin d → ℤ)}
    (b : Module.Basis (Fin d) ℤ H) (c : Fin d → ℤ) (k : Fin d) :
    ((b.equivFun.symm c : H) : Fin d → ℤ) k
      = ∑ i, c i * ((b i : Fin d → ℤ) k) := by
  rw [Module.Basis.equivFun_symm_apply]
  have hcoe : (((∑ i, c i • b i : H)) : Fin d → ℤ)
      = ∑ i, c i • ((b i : Fin d → ℤ)) := by
    simp
  rw [hcoe]
  simp [Finset.sum_apply]

/-- **The chart formula**: the Gaussian mass of a full-rank subgroup
is the Boltzmann sum of its pulled-back Gram form. -/
theorem subMass_eq_gramTheta {H : AddSubgroup (Fin d → ℤ)} (s : ℝ)
    (b : Module.Basis (Fin d) ℤ H) :
    subMass s H = gramTheta (subGram b) s := by
  rw [subMass, gramTheta, ← (b.equivFun.symm.toEquiv).tsum_eq]
  refine tsum_congr fun c => ?_
  congr 1
  have hc : ∀ k, ((((b.equivFun.symm c : H) : Fin d → ℤ) k : ℤ) : ℝ)
      = ∑ i, (c i : ℝ) * (((b i : Fin d → ℤ) k : ℤ) : ℝ) := by
    intro k
    rw [coe_equivFun_symm]
    push_cast
    ring
  have henergy :
      (∑ k, ((((b.equivFun.symm c : H) : Fin d → ℤ) k : ℤ) : ℝ) ^ 2)
        = ∑ i, ∑ j, subGram b i j * (c i : ℝ) * (c j : ℝ) := by
    calc
      (∑ k, ((((b.equivFun.symm c : H) : Fin d → ℤ) k : ℤ) : ℝ) ^ 2)
        = ∑ k, ∑ i, ∑ j, ((c i : ℝ) * (((b i : Fin d → ℤ) k : ℤ) : ℝ))
            * ((c j : ℝ) * (((b j : Fin d → ℤ) k : ℤ) : ℝ)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hc k, sq, Finset.sum_mul_sum]
      _ = ∑ i, ∑ j, ∑ k, ((c i : ℝ) * (((b i : Fin d → ℤ) k : ℤ) : ℝ))
            * ((c j : ℝ) * (((b j : Fin d → ℤ) k : ℤ) : ℝ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, subGram b i j * (c i : ℝ) * (c j : ℝ) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          rw [subGram_apply, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  show -s * (∑ k, ((((b.equivFun.symm c : H) : Fin d → ℤ) k : ℤ) : ℝ) ^ 2)
      = -s * ∑ i, ∑ j, subGram b i j * (c i : ℝ) * (c j : ℝ)
  rw [henergy]

/-! ## The mass ratio at a finite-index inclusion -/

theorem subMass_pos {H : AddSubgroup (Fin d → ℤ)} (hidx : H.index ≠ 0)
    (b : Module.Basis (Fin d) ℤ H) {s : ℝ} (hs : 0 < s) :
    0 < subMass s H := by
  rw [subMass_eq_gramTheta s b]
  exact gramTheta_pos (subGram_posDef hidx b) hs

/-- **The finite-index mass ratio**: for a full-rank finite-index
inclusion `V ≤ U` of the integer lattice the Gaussian masses compare,
at small scale, by the relative index. -/
theorem tendsto_subMass_ratio_chart {U V : AddSubgroup (Fin d → ℤ)}
    (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) (bU : Module.Basis (Fin d) ℤ U)
    (bV : Module.Basis (Fin d) ℤ V) :
    Tendsto (fun s => subMass s U / subMass s V) (𝓝[>] (0 : ℝ))
      (𝓝 (((V.relIndex U : ℕ) : ℝ))) := by
  have hUR : (0 : ℝ) < (U.index : ℝ) := by
    have : 0 < U.index := Nat.pos_of_ne_zero hU
    exact_mod_cast this
  have hratio := tendsto_gramTheta_ratio (subGram_posDef hU bU)
    (subGram_posDef hV bV)
  have hval : ((subGram bV).det / (subGram bU).det) ^ ((1 : ℝ) / 2)
      = ((V.relIndex U : ℕ) : ℝ) := by
    have hx : (0 : ℝ) ≤ (V.index : ℝ) / (U.index : ℝ) := by positivity
    have hrel : ((V.relIndex U : ℕ) : ℝ) * (U.index : ℝ) = (V.index : ℝ) := by
      exact_mod_cast AddSubgroup.relIndex_mul_index hle
    rw [det_subGram bV, det_subGram bU, ← div_pow, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul hx]
    norm_num
    field_simp
    linarith [hrel]
  rw [hval] at hratio
  exact hratio.congr fun s => by
    rw [subMass_eq_gramTheta s bU, subMass_eq_gramTheta s bV]

/-- **The logarithmic form**: the gap between the two log-masses
converges to the logarithm of the relative index. This is the field
gap the order-three recurrence consumes. -/
theorem tendsto_log_subMass_sub_chart {U V : AddSubgroup (Fin d → ℤ)}
    (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) (bU : Module.Basis (Fin d) ℤ U)
    (bV : Module.Basis (Fin d) ℤ V) :
    Tendsto (fun s => Real.log (subMass s U) - Real.log (subMass s V))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (((V.relIndex U : ℕ) : ℝ)))) := by
  have hrel : V.relIndex U ≠ 0 := by
    intro h
    apply hV
    have := AddSubgroup.relIndex_mul_index hle
    rw [h, zero_mul] at this
    exact this.symm
  have hrelR : (0 : ℝ) < ((V.relIndex U : ℕ) : ℝ) := by
    have : 0 < V.relIndex U := Nat.pos_of_ne_zero hrel
    exact_mod_cast this
  have hcomp := (Real.continuousAt_log hrelR.ne').tendsto.comp
    (tendsto_subMass_ratio_chart hle hU hV bU bV)
  refine hcomp.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
    fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  show Real.log (subMass s U / subMass s V)
    = Real.log (subMass s U) - Real.log (subMass s V)
  exact Real.log_div (subMass_pos hU bU hs').ne' (subMass_pos hV bV hs').ne'

/-! ## The intrinsic form -/

/-- A chart for any finite-index subgroup: a finite-index subgroup of
the integer lattice is itself free of the ambient rank, so the
standard basis transports to it. -/
noncomputable def subBasis {H : AddSubgroup (Fin d → ℤ)} (hH : H.index ≠ 0) :
    Module.Basis (Fin d) ℤ H :=
  (Pi.basisFun ℤ (Fin d)).map
    (Int.addSubgroup_index_ne_zero_iff.mp hH).some.toIntLinearEquiv.symm

theorem subMass_pos' {H : AddSubgroup (Fin d → ℤ)} (hidx : H.index ≠ 0)
    {s : ℝ} (hs : 0 < s) : 0 < subMass s H :=
  subMass_pos hidx (subBasis hidx) hs

/-- **The finite-index mass ratio**, chart-free: for a finite-index
inclusion of the integer lattice the Gaussian masses compare, at
small scale, by the relative index. -/
theorem tendsto_subMass_ratio {U V : AddSubgroup (Fin d → ℤ)} (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) :
    Tendsto (fun s => subMass s U / subMass s V) (𝓝[>] (0 : ℝ))
      (𝓝 (((V.relIndex U : ℕ) : ℝ))) :=
  tendsto_subMass_ratio_chart hle hU hV (subBasis hU) (subBasis hV)

/-- **The logarithmic form**, chart-free. -/
theorem tendsto_log_subMass_sub {U V : AddSubgroup (Fin d → ℤ)} (hle : V ≤ U)
    (hU : U.index ≠ 0) (hV : V.index ≠ 0) :
    Tendsto (fun s => Real.log (subMass s U) - Real.log (subMass s V))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (((V.relIndex U : ℕ) : ℝ)))) :=
  tendsto_log_subMass_sub_chart hle hU hV (subBasis hU) (subBasis hV)

end Theaetetus
