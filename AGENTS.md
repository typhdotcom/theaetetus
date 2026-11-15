# Theaetetus

Read `README.md` first — the object, the theorems, the open
questions, and the standards.

Ground rules, restated for every session:

- Zero `sorry`, zero `axiom` declarations; `lake build` green is
  the only definition of done (`nu tasks.nu check`).
- The root module `Theaetetus.lean` is the map: every module is
  imported there under a one-line section comment, in logical
  order. New modules join that list; no markdown duplicates it —
  the compiled import list is the only index.
- Vocabulary is arithmetic and information-theoretic — defect,
  carrier, resolution, tower, pairing, complexity.
- Where a desired statement fails, keep the counterexample as a
  theorem.
- References are one-way: prose may cite Lean names; Lean never
  cites prose. No README sections, roadmap targets, rung or
  Q-numbers in docstrings or comments — state the mathematics and
  cite theorem names only.
