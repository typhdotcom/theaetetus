import Mathlib.Logic.Equiv.Basic

/-! # The Pullback Substrate

Fibers, fiber products, the pullback with its base map, and the
sigma-fiber factorization that decomposes it. -/

namespace Theaetetus

universe u

/-! ## Pullback Infrastructure -/

/-- The fiber of a function over a point. -/
abbrev Fiber {A D : Type u} (f : A → D) (d : D) : Type u :=
  { a : A // f a = d }

/-- The product of fibers over a common base point. -/
abbrev FiberProd {A B D : Type u} (f : A → D) (g : B → D) (d : D) : Type u :=
  Fiber f d × Fiber g d

/-- The pullback (fiber product) of two types over a shared base. -/
def Pullback {A B D : Type u} (f : A → D) (g : B → D) : Type u :=
  { p : A × B // f p.1 = g p.2 }

/-- The shared base value of a pullback element. -/
def Pullback.base {A B D : Type u} {f : A → D} {g : B → D} (p : Pullback f g) : D :=
  f p.val.1

/-- The fundamental equivalence: pullback factors through sigma of fiber products. -/
def Pullback.equivSigmaFiber {A B D : Type u} (f : A → D) (g : B → D) :
    Pullback f g ≃ Σ d : D, FiberProd f g d where
  toFun p := ⟨p.base, ⟨p.val.1, rfl⟩, ⟨p.val.2, p.property.symm ▸ rfl⟩⟩
  invFun x := ⟨(x.2.1.val, x.2.2.val), x.2.1.property.trans x.2.2.property.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv := fun ⟨_, ⟨_, ha⟩, ⟨_, hb⟩⟩ => by subst ha; rfl

end Theaetetus
