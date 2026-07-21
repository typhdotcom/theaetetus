# Theaetetus

Read `PROGRAM.md` before doing anything — it is the charter: the
seed theorem, the research questions, the copy-map, the vocabulary,
and the milestones.

Ground rules, restated for every session:

- **Meno (`~/dev/meno`) is a quarry, not an upstream.** You may
  read it and copy proofs verbatim (mark them
  `-- ported from Meno/<file>`). No lake dependency on it, no
  imports from it, no syncing in either direction.
- **No physics vocabulary.** "Gravity", "matter", "universe" stay
  in Meno. This project studies *the defect* `D(q, q′)` on the
  divisibility lattice. Names per PROGRAM.md's vocabulary table.
- Zero `sorry`, zero `axiom` declarations; `lake build` green is
  the only definition of done. Toolchain and Mathlib pins per
  PROGRAM.md's standards section.
- Version control is jujutsu: `jj status`, `jj diff --git`,
  `jj commit -m "..."`.
