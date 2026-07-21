import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Theaetetus

The arithmetic of coupled resolutions. See `PROGRAM.md` for the
charter: the object of study is the defect `D(q, q′)` on the
divisibility lattice of a positive-definite integral quadratic form.

This file is the M0 scaffold: it pins the toolchain and Mathlib and
verifies the build pipeline end-to-end. The scalar layer
(`SectorAction`, `θ`) lands here next, per the copy-map.
-/

namespace Theaetetus

/-- Scaffold check: the pinned Mathlib is importable and usable. -/
example : Real.log 1 = 0 := Real.log_one

end Theaetetus
