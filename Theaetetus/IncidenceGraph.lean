import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Incidence Graphs: the one graph substrate

The single finite-multigraph foundation under every presentation. An
`IncidenceGraph` bundles finite vertex
and edge types with source and target maps; the boundary, gradient,
and their linear-map forms are defined **once**, over an arbitrary
commutative ring — `ℝ`, `ℤ`, and `ZMod q` are the consumers.

Beyond the chain-level vocabulary this file provides the engines built
on it:

* **Walks** (`Walk`, `Walk.sum`, `Walk.chain`): edge paths traversed
  forward or backward, their cochain sums, and their signed traversal
  chains. Closed walks have closed chains (`Walk.boundary_chain`), and
  a walk's sum is its chain pairing (`Walk.sum_eq_dotProduct`).
* **Components and gauge** (`Components`, `finrank_gauge`): vertices
  modulo reachability; the kernel of the gradient is exactly the
  locally constant functions, so its dimension is the component
  count. Connectivity governs the gauge sector — never exactness.
* **Walk integration** (`integrate`, `grad_integrate`): a cochain all
  of whose closed-walk sums vanish is a gradient, by integrating
  along chosen walks from component basepoints. Over `ℤ` this is the
  integral-potentials engine that the fundamental presentation
  feeds; over `ℝ` it powers spanning. This is where walk structure
  enters the theory — which is why it lives here, on the graph, and
  not on any presentation. -/

namespace Theaetetus

open scoped BigOperators
open Matrix

universe u v

/-- A finite directed multigraph: finite vertex and edge types with
source and target maps. The one graph substrate. -/
structure IncidenceGraph where
  /-- Vertices. -/
  V : Type u
  /-- Edges. -/
  E : Type u
  [fintypeV : Fintype V]
  [fintypeE : Fintype E]
  [decEqV : DecidableEq V]
  [decEqE : DecidableEq E]
  /-- Edge source. -/
  src : E → V
  /-- Edge target. -/
  tgt : E → V

attribute [instance] IncidenceGraph.fintypeV IncidenceGraph.fintypeE
  IncidenceGraph.decEqV IncidenceGraph.decEqE

/-- Net flow of an `R`-valued 1-cochain into a vertex, for edge data
`(src, tgt)`: each edge contributes `+ω e` at its target and `−ω e`
at its source. Defined once, over any commutative ring. -/
def flowBoundary {V : Type u} {ι : Type v} [Fintype ι] [DecidableEq V]
    {R : Type*} [CommRing R] (src tgt : ι → V) (ω : ι → R) (v : V) : R :=
  ∑ e, ((if tgt e = v then (1 : R) else 0)
    - (if src e = v then (1 : R) else 0)) * ω e

namespace IncidenceGraph

variable (G : IncidenceGraph.{u})
variable {R : Type*} [CommRing R]

/-! ## Boundary and gradient, once -/

/-- The coefficient of edge `e` in the boundary at vertex `v`. -/
def bcoeff (v : G.V) (e : G.E) : R :=
  (if G.tgt e = v then (1 : R) else 0) - (if G.src e = v then 1 else 0)

theorem bcoeff_def (v : G.V) (e : G.E) :
    G.bcoeff v e = (if G.tgt e = v then (1 : R) else 0)
      - (if G.src e = v then 1 else 0) := rfl

/-- The boundary of a 1-cochain: net flow into each vertex. -/
def boundary (ω : G.E → R) (v : G.V) : R :=
  flowBoundary G.src G.tgt ω v

theorem boundary_eq_sum (ω : G.E → R) (v : G.V) :
    G.boundary ω v = ∑ e, G.bcoeff v e * ω e := rfl

theorem boundary_zero (v : G.V) : G.boundary (0 : G.E → R) v = 0 := by
  rw [boundary_eq_sum]
  exact Finset.sum_eq_zero fun e _ => by
    rw [show (0 : G.E → R) e = 0 from rfl, mul_zero]

theorem boundary_add (ω η : G.E → R) (v : G.V) :
    G.boundary (ω + η) v = G.boundary ω v + G.boundary η v := by
  rw [boundary_eq_sum, boundary_eq_sum, boundary_eq_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by
    rw [show (ω + η) e = ω e + η e from rfl, mul_add]

theorem boundary_smul (c : R) (ω : G.E → R) (v : G.V) :
    G.boundary (c • ω) v = c * G.boundary ω v := by
  rw [boundary_eq_sum, boundary_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by
    rw [show (c • ω) e = c * ω e from rfl]
    ring

theorem boundary_neg (ω : G.E → R) (v : G.V) :
    G.boundary (-ω) v = -G.boundary ω v := by
  have h := G.boundary_add (-ω) ω v
  rw [neg_add_cancel, G.boundary_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The boundary of a single-edge indicator is that edge's boundary
coefficient. -/
theorem boundary_single (e : G.E) (w : G.V) :
    G.boundary (Pi.single e (1 : R)) w = G.bcoeff w e := by
  have hfun : ∀ e', (G.bcoeff w e' : R) * (Pi.single e (1 : R) : G.E → R) e'
      = if e' = e then (G.bcoeff w e' : R) else 0 := fun e' => by
    rcases eq_or_ne e' e with h | h
    · subst h
      rw [if_pos rfl, Pi.single_eq_same, mul_one]
    · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]
  rw [boundary_eq_sum, Finset.sum_congr rfl fun e' _ => hfun e',
    Finset.sum_ite_eq' Finset.univ e (fun e' => G.bcoeff w e')]
  simp

/-- The gradient (coboundary) of a vertex potential. -/
def grad (f : G.V → R) : G.E → R :=
  fun e => f (G.tgt e) - f (G.src e)

/-- The gradient as a linear map — defined once, over any commutative
ring; `ℝ`, `ℤ`, `ZMod q` are the consumers. -/
def gradLin (R : Type*) [CommRing R] : (G.V → R) →ₗ[R] (G.E → R) where
  toFun := G.grad
  map_add' f g := funext fun e => by
    show (f + g) (G.tgt e) - (f + g) (G.src e)
      = (f (G.tgt e) - f (G.src e)) + (g (G.tgt e) - g (G.src e))
    simp only [Pi.add_apply]
    ring
  map_smul' c f := funext fun e => by
    show (c • f) (G.tgt e) - (c • f) (G.src e)
      = c • (f (G.tgt e) - f (G.src e))
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem gradLin_apply (f : G.V → R) : G.gradLin R f = G.grad f := rfl

/-- The boundary as a linear map — `∂` over any commutative ring. -/
def boundaryLin (R : Type*) [CommRing R] : (G.E → R) →ₗ[R] (G.V → R) where
  toFun ω := G.boundary ω
  map_add' ω η := funext fun v => G.boundary_add ω η v
  map_smul' c ω := funext fun v => G.boundary_smul c ω v

@[simp] theorem boundaryLin_apply (ω : G.E → R) :
    G.boundaryLin R ω = G.boundary ω := rfl

/-- The boundary matrix: rows are vertices, columns are edges. -/
def boundaryMatrix (R : Type*) [CommRing R] : Matrix G.V G.E R :=
  Matrix.of fun v e => (if G.tgt e = v then (1 : R) else 0)
    - (if G.src e = v then (1 : R) else 0)

theorem boundaryMatrix_mulVec (ω : G.E → R) (v : G.V) :
    (G.boundaryMatrix R *ᵥ ω) v = G.boundary ω v := rfl

private lemma sum_ite_one_mul (f : G.V → R) (a : G.V) :
    ∑ v, (if a = v then (1 : R) else 0) * f v = f a := by
  rw [show (fun v => (if a = v then (1 : R) else 0) * f v)
      = fun v => if a = v then f v else 0 from funext fun v => by
    by_cases h : a = v
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]]
  rw [Finset.sum_ite_eq Finset.univ a f]
  simp

/-- The transpose of the boundary matrix computes the gradient. -/
theorem transpose_boundaryMatrix_mulVec (f : G.V → R) :
    (G.boundaryMatrix R)ᵀ *ᵥ f = G.grad f := by
  funext e
  show ∑ v, ((if G.tgt e = v then (1 : R) else 0)
      - (if G.src e = v then (1 : R) else 0)) * f v
    = f (G.tgt e) - f (G.src e)
  calc ∑ v, ((if G.tgt e = v then (1 : R) else 0)
        - (if G.src e = v then (1 : R) else 0)) * f v
      = (∑ v, (if G.tgt e = v then (1 : R) else 0) * f v)
        - ∑ v, (if G.src e = v then (1 : R) else 0) * f v := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = f (G.tgt e) - f (G.src e) := by
        rw [G.sum_ite_one_mul f (G.tgt e), G.sum_ite_one_mul f (G.src e)]

/-- **Discrete Stokes / summation by parts**, once, over any
commutative ring: pairing a gradient against a cochain is pairing the
potential against the boundary. -/
theorem grad_dotProduct_eq (f : G.V → R) (ω : G.E → R) :
    G.grad f ⬝ᵥ ω = ∑ v, f v * G.boundary ω v := by
  rw [← G.transpose_boundaryMatrix_mulVec f]
  calc ((G.boundaryMatrix R)ᵀ *ᵥ f) ⬝ᵥ ω
      = (f ᵥ* G.boundaryMatrix R) ⬝ᵥ ω := by rw [Matrix.mulVec_transpose]
    _ = f ⬝ᵥ (G.boundaryMatrix R *ᵥ ω) :=
        (Matrix.dotProduct_mulVec f (G.boundaryMatrix R) ω).symm
    _ = ∑ v, f v * G.boundary ω v := by
        show ∑ v, f v * (G.boundaryMatrix R *ᵥ ω) v = _
        exact Finset.sum_congr rfl fun v _ => by rw [G.boundaryMatrix_mulVec]

/-! ## Walks -/

/-- A walk from `u` to `v`: a sequence of edges, each traversed
forward (`consF`) or backward (`consB`). -/
inductive Walk : G.V → G.V → Type u
  | nil (v : G.V) : Walk v v
  | consF (e : G.E) {v : G.V} (p : Walk (G.tgt e) v) : Walk (G.src e) v
  | consB (e : G.E) {v : G.V} (p : Walk (G.src e) v) : Walk (G.tgt e) v

variable {G}

namespace Walk

/-- Concatenation of walks. -/
def append : ∀ {u v w : G.V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, .nil _, q => q
  | _, _, _, .consF e p, q => .consF e (p.append q)
  | _, _, _, .consB e p, q => .consB e (p.append q)

/-- Reversal of a walk. -/
def reverse : ∀ {u v : G.V}, G.Walk u v → G.Walk v u
  | _, _, .nil v => .nil v
  | _, _, .consF e p => p.reverse.append (.consB e (.nil _))
  | _, _, .consB e p => p.reverse.append (.consF e (.nil _))

/-- The `ω`-sum along a walk: `+ω e` per forward and `−ω e` per
backward traversal. -/
def sum (ω : G.E → R) : ∀ {u v : G.V}, G.Walk u v → R
  | _, _, .nil _ => 0
  | _, _, .consF e p => ω e + p.sum ω
  | _, _, .consB e p => -ω e + p.sum ω

theorem sum_append (ω : G.E → R) :
    ∀ {u v w : G.V} (p : G.Walk u v) (q : G.Walk v w),
      (p.append q).sum ω = p.sum ω + q.sum ω
  | _, _, _, .nil _, q => by
      show q.sum ω = 0 + q.sum ω
      ring
  | _, _, _, .consF e p, q => by
      show ω e + (p.append q).sum ω = (ω e + p.sum ω) + q.sum ω
      rw [sum_append ω p q]
      ring
  | _, _, _, .consB e p, q => by
      show -ω e + (p.append q).sum ω = (-ω e + p.sum ω) + q.sum ω
      rw [sum_append ω p q]
      ring

theorem sum_reverse (ω : G.E → R) :
    ∀ {u v : G.V} (p : G.Walk u v), p.reverse.sum ω = -(p.sum ω)
  | _, _, .nil _ => by
      show (0 : R) = -0
      ring
  | _, _, .consF e p => by
      show (p.reverse.append (.consB e (.nil _))).sum ω = -(ω e + p.sum ω)
      rw [sum_append, sum_reverse ω p]
      show -p.sum ω + (-ω e + 0) = -(ω e + p.sum ω)
      ring
  | _, _, .consB e p => by
      show (p.reverse.append (.consF e (.nil _))).sum ω = -(-ω e + p.sum ω)
      rw [sum_append, sum_reverse ω p]
      show -p.sum ω + (ω e + 0) = -(-ω e + p.sum ω)
      ring

/-- Transporting a walk along an equality of start points does not
change its sum. -/
theorem sum_cast (ω : G.E → R) {u u' v : G.V} (h : u = u')
    (p : G.Walk u v) : (h ▸ p : G.Walk u' v).sum ω = p.sum ω := by
  cases h
  rfl

omit [CommRing R] in
/-- A function with edge-wise vanishing gradient is constant along
every walk. -/
theorem apply_eq {f : G.V → R} (hf : ∀ e, f (G.tgt e) = f (G.src e)) :
    ∀ {u v : G.V}, G.Walk u v → f u = f v
  | _, _, .nil _ => rfl
  | _, _, .consF e p => (hf e).symm.trans (apply_eq hf p)
  | _, _, .consB e p => (hf e).trans (apply_eq hf p)

/-- The signed traversal chain of a walk: net crossings per edge. -/
def chain (R : Type*) [CommRing R] :
    ∀ {u v : G.V}, G.Walk u v → (G.E → R)
  | _, _, .nil _ => 0
  | _, _, .consF e p => Pi.single e 1 + p.chain R
  | _, _, .consB e p => -Pi.single e 1 + p.chain R

private lemma dotProduct_single_one (ω : G.E → R) (e : G.E) :
    ω ⬝ᵥ (Pi.single e (1 : R) : G.E → R) = ω e := by
  have hfun : ∀ e', ω e' * (Pi.single e (1 : R) : G.E → R) e'
      = if e' = e then ω e' else 0 := fun e' => by
    rcases eq_or_ne e' e with h | h
    · subst h
      rw [if_pos rfl, Pi.single_eq_same, mul_one]
    · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]
  show ∑ e', ω e' * (Pi.single e (1 : R) : G.E → R) e' = ω e
  rw [Finset.sum_congr rfl fun e' _ => hfun e',
    Finset.sum_ite_eq' Finset.univ e ω]
  simp

/-- A walk's sum is the pairing of the cochain with its chain. -/
theorem sum_eq_dotProduct (ω : G.E → R) :
    ∀ {u v : G.V} (p : G.Walk u v), p.sum ω = ω ⬝ᵥ p.chain R
  | _, _, .nil _ => by
      show (0 : R) = ω ⬝ᵥ (0 : G.E → R)
      rw [dotProduct_zero]
  | _, _, .consF e p => by
      show ω e + p.sum ω = ω ⬝ᵥ (Pi.single e 1 + p.chain R)
      rw [dotProduct_add, dotProduct_single_one, sum_eq_dotProduct ω p]
  | _, _, .consB e p => by
      show -ω e + p.sum ω = ω ⬝ᵥ (-Pi.single e 1 + p.chain R)
      rw [dotProduct_add, dotProduct_neg, dotProduct_single_one,
        sum_eq_dotProduct ω p]

/-- The integer chain casts to the `R`-valued chain. -/
theorem chain_cast :
    ∀ {u v : G.V} (p : G.Walk u v) (e : G.E),
      ((p.chain ℤ e : ℤ) : R) = p.chain R e
  | _, _, .nil _, e => by
      show (((0 : G.E → ℤ) e : ℤ) : R) = (0 : G.E → R) e
      simp
  | _, _, .consF e' p, e => by
      show ((((Pi.single e' 1 + p.chain ℤ : G.E → ℤ)) e : ℤ) : R)
        = ((Pi.single e' 1 + p.chain R : G.E → R)) e
      rw [Pi.add_apply, Pi.add_apply, Int.cast_add, chain_cast p e]
      congr 1
      rcases eq_or_ne e e' with h | h
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same, Int.cast_one]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Int.cast_zero]
  | _, _, .consB e' p, e => by
      show ((((-Pi.single e' 1 + p.chain ℤ : G.E → ℤ)) e : ℤ) : R)
        = ((-Pi.single e' 1 + p.chain R : G.E → R)) e
      rw [Pi.add_apply, Pi.add_apply, Int.cast_add, chain_cast p e]
      congr 1
      rw [Pi.neg_apply, Pi.neg_apply, Int.cast_neg]
      congr 1
      rcases eq_or_ne e e' with h | h
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same, Int.cast_one]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Int.cast_zero]

/-- The boundary of a walk's chain: `+1` at the endpoint, `−1` at the
start — so closed walks have closed chains. -/
theorem boundary_chain :
    ∀ {u v : G.V} (p : G.Walk u v) (w : G.V),
      G.boundary (p.chain R) w
        = (if v = w then (1 : R) else 0) - (if u = w then 1 else 0)
  | _, _, .nil x, w => by
      show G.boundary (0 : G.E → R) w = _
      rw [G.boundary_zero]
      ring
  | _, _, .consF e p, w => by
      show G.boundary (Pi.single e 1 + p.chain R) w = _
      rw [G.boundary_add, G.boundary_single, boundary_chain p w,
        G.bcoeff_def]
      ring
  | _, _, .consB e p, w => by
      show G.boundary (-Pi.single e 1 + p.chain R) w = _
      rw [G.boundary_add, G.boundary_neg, G.boundary_single,
        boundary_chain p w, G.bcoeff_def]
      ring

/-- A closed walk's chain is closed: it lies in the kernel of the
boundary. -/
theorem boundary_chain_closed {v : G.V} (p : G.Walk v v) (w : G.V) :
    G.boundary (p.chain R) w = 0 := by
  rw [p.boundary_chain w]
  ring

end Walk

variable (G)

/-! ## Components and gauge -/

/-- Reachability: some walk connects the two vertices. -/
def Reaches (u v : G.V) : Prop := Nonempty (G.Walk u v)

/-- Reachability is an equivalence. -/
def compSetoid : Setoid G.V where
  r := G.Reaches
  iseqv :=
    ⟨fun v => ⟨.nil v⟩,
     fun ⟨p⟩ => ⟨p.reverse⟩,
     fun ⟨p⟩ ⟨q⟩ => ⟨p.append q⟩⟩

/-- The connected components: vertices modulo reachability. -/
def Components : Type u := Quotient G.compSetoid

instance : Finite G.Components := Quotient.finite _

noncomputable instance : Fintype G.Components := Fintype.ofFinite _

/-- The number of connected components. -/
noncomputable def componentCard : ℕ := Nat.card G.Components

/-- A walk-preconnected graph with a vertex has exactly one
component. -/
theorem componentCard_eq_one (hne : Nonempty G.V)
    (h : ∀ u v : G.V, G.Reaches u v) : G.componentCard = 1 := by
  obtain ⟨v⟩ := hne
  have hsub : Subsingleton G.Components :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun u w => Quotient.sound (h u w)⟩
  have : Unique G.Components :=
    ⟨⟨Quotient.mk G.compSetoid v⟩, fun _ => Subsingleton.elim _ _⟩
  show Nat.card G.Components = 1
  exact Nat.card_unique

/-- The gauge sector is the locally constant functions: the kernel of
the gradient is linearly equivalent to functions on the components. -/
noncomputable def gaugeEquiv :
    LinearMap.ker (G.gradLin ℝ) ≃ₗ[ℝ] (G.Components → ℝ) where
  toFun f := Quotient.lift (f : G.V → ℝ)
    (fun _ _ ⟨p⟩ => Walk.apply_eq
      (fun e => sub_eq_zero.mp
        (congrFun (LinearMap.mem_ker.mp f.2) e)) p)
  map_add' f g := funext <| Quotient.ind fun _ => rfl
  map_smul' c f := funext <| Quotient.ind fun _ => rfl
  invFun h :=
    ⟨fun v => h (Quotient.mk G.compSetoid v), LinearMap.mem_ker.mpr (by
      funext e
      show h (Quotient.mk G.compSetoid (G.tgt e))
        - h (Quotient.mk G.compSetoid (G.src e)) = 0
      have hstep : Quotient.mk G.compSetoid (G.src e)
          = Quotient.mk G.compSetoid (G.tgt e) :=
        Quotient.sound
          (⟨.consF e (.nil _)⟩ : G.Reaches (G.src e) (G.tgt e))
      rw [← hstep]
      ring)⟩
  left_inv f := Subtype.ext (funext fun _ => rfl)
  right_inv h := funext <| Quotient.ind fun _ => rfl

/-- **The gauge theorem**: the dimension of the
gradient's kernel is the number of connected components. Connectivity
governs gauge, never exactness. -/
theorem finrank_gauge :
    Module.finrank ℝ (LinearMap.ker (G.gradLin ℝ)) = G.componentCard := by
  rw [G.gaugeEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact Nat.card_eq_fintype_card.symm

/-! ## Walk integration -/

/-- A chosen basepoint for each vertex's component. -/
noncomputable def basePoint (v : G.V) : G.V :=
  (Quotient.mk G.compSetoid v).out

theorem reaches_basePoint (v : G.V) : G.Reaches (G.basePoint v) v :=
  Quotient.exact (Quotient.out_eq (Quotient.mk G.compSetoid v))

/-- A chosen walk from the component basepoint to each vertex. -/
noncomputable def walkFromBase (v : G.V) : G.Walk (G.basePoint v) v :=
  (G.reaches_basePoint v).some

/-- Integration of a cochain from the component basepoints along the
chosen walks. -/
noncomputable def integrate (ω : G.E → R) (v : G.V) : R :=
  (G.walkFromBase v).sum ω

/-- Two walks between the same endpoints have the same sum, provided
all closed-walk sums vanish. -/
theorem sum_eq_of_closed (ω : G.E → R)
    (hω : ∀ (w : G.V) (c : G.Walk w w), c.sum ω = 0)
    {u v : G.V} (p q : G.Walk u v) : p.sum ω = q.sum ω := by
  have h := hω u (p.append q.reverse)
  rw [Walk.sum_append, Walk.sum_reverse] at h
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)

/-- **Walk integration**: a cochain whose closed-walk sums all vanish
is a gradient — over any commutative ring. At `ℤ` this is the
integral-potentials engine; at `ℝ`, the spanning engine. -/
theorem grad_integrate (ω : G.E → R)
    (hω : ∀ (w : G.V) (c : G.Walk w w), c.sum ω = 0) :
    G.grad (G.integrate ω) = ω := by
  funext e
  show G.integrate ω (G.tgt e) - G.integrate ω (G.src e) = ω e
  have hbase : G.basePoint (G.src e) = G.basePoint (G.tgt e) := by
    unfold basePoint
    congr 1
    exact Quotient.sound ⟨.consF e (.nil _)⟩
  have key := G.sum_eq_of_closed ω hω
    (hbase ▸ ((G.walkFromBase (G.src e)).append (.consF e (.nil _))))
    (G.walkFromBase (G.tgt e))
  rw [Walk.sum_cast, Walk.sum_append] at key
  show (G.walkFromBase (G.tgt e)).sum ω
    - (G.walkFromBase (G.src e)).sum ω = ω e
  rw [← key]
  show (G.walkFromBase (G.src e)).sum ω + (ω e + 0)
    - (G.walkFromBase (G.src e)).sum ω = ω e
  ring

/-! ## The integral cycle lattice and the first Betti number

Pure topology: the lattice `H₁(G;ℤ) = ker ∂ℤ` and its rank `b₁` are
intrinsic to the graph — defined here, in the substrate. The
fundamental-basis theorem (`GraphHomology.lean`) **consumes** this
invariant: it constructs a basis of this lattice and proves the
construction has exactly `b₁` elements (`cycleBasisSigma_fst`). -/

section CycleLattice

variable (G : IncidenceGraph.{u})

/-- Casting an integer cochain commutes with the boundary. -/
theorem boundary_castR (ω : G.E → ℤ) (v : G.V) :
    G.boundary (fun e => ((ω e : ℤ) : ℝ)) v = ((G.boundary ω v : ℤ) : ℝ) := by
  rw [boundary_eq_sum, boundary_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  rw [G.bcoeff_def, G.bcoeff_def]
  push_cast [apply_ite (Int.cast : ℤ → ℝ)]
  norm_num

/-- The boundary commutes with any ring homomorphism on coefficients
— the scalar-extension engine. -/
theorem boundary_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ω : G.E → R) (v : G.V) :
    f (G.boundary ω v) = G.boundary (fun e => f (ω e)) v := by
  rw [boundary_eq_sum, boundary_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul]
  congr 1
  rw [G.bcoeff_def, G.bcoeff_def, map_sub]
  congr 1
  · rw [apply_ite f, map_one, map_zero]
  · rw [apply_ite f, map_one, map_zero]

/-- The integral cycle lattice: `H₁(G;ℤ) = ker ∂ℤ`. -/
def cycleLattice : Submodule ℤ (G.E → ℤ) := LinearMap.ker (G.boundaryLin ℤ)

theorem mem_cycleLattice {ω : G.E → ℤ} :
    ω ∈ G.cycleLattice ↔ ∀ v, G.boundary ω v = 0 := by
  rw [cycleLattice, LinearMap.mem_ker]
  constructor
  · intro h v
    exact congrFun h v
  · intro h
    funext v
    exact h v

/-- Chains of closed walks are cycles. -/
theorem chain_mem_cycleLattice {w : G.V} (c : G.Walk w w) :
    c.chain ℤ ∈ G.cycleLattice :=
  G.mem_cycleLattice.mpr (Walk.boundary_chain_closed c)


/-- **Saturation**: the cycle lattice is division-closed — a multiple
of a cochain is a cycle only if the cochain is. This is where
torsion-freeness of `ℤ^E ⧸ H₁` comes from. -/
theorem mem_of_smul_mem {c : ℤ} (hc : c ≠ 0) {x : G.E → ℤ}
    (h : c • x ∈ G.cycleLattice) : x ∈ G.cycleLattice := by
  rw [mem_cycleLattice] at h ⊢
  intro v
  have hv := h v
  rw [G.boundary_smul] at hv
  rcases mul_eq_zero.mp hv with h0 | h0
  · exact absurd h0 hc
  · exact h0


/-- **The first Betti number, intrinsically**: the rank of the
integral cycle lattice. No presentation, no chosen basis — this is
the invariant every lattice basis meets (`card_eq_b1`,
`GraphHomology.lean`). -/
noncomputable def b1 : ℕ := Module.finrank ℤ G.cycleLattice

end CycleLattice

end IncidenceGraph

/-- The cycle graph `C_n`: vertices and edges `Fin n`, edge
`e : e → e + 1`. -/
@[reducible] def cycleGraph (n : ℕ) (hn : 0 < n) : IncidenceGraph :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { V := Fin n
    E := Fin n
    src := fun e => e
    tgt := fun e => e + 1 }

end Theaetetus
