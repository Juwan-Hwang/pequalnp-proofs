# WIP: L-meta-3786 partial proof (Finch, 2026-11-26)

Released back to the desk 2026-11-26 ~23:45 CST with reason `missing_lemma`.
Nothing was submitted.

## State
- `lean/PEqualNP/Outside/L_meta_3786.lean` — 1341 lines, compiles clean
  EXCEPT the main theorem, which is still `sorry` (last line).
- Verified pieces: `pairCleanBound` (adapted from L_meta_1602), graph section
  (C4-free, degrees 4/3, 36 edges, tau >= 9 via matching), and the conversion
  `eval_iff_edgeTrue` (statement A/B quantification <-> graph edge-OR on Fin 21).
- Remaining blocker: the main theorem needs 2-cleanliness of the circuit,
  which requires TopForm normalization + junk elimination (repo material in
  L_meta_1499/1528/4747, ~7000 lines with intricate hypotheses) adapted to
  this statement. That adaptation was not attempted.

## Environment note (important)
Full `import Mathlib` builds thrash in this VM (6.2GB oleans vs ~6GB RAM;
a 60-min build produced 0 output). Iterate with narrowed imports instead:
`Mathlib.Combinatorics.SimpleGraph.DegreeSum` + `Mathlib.Data.Finset.Card` +
`Mathlib.Tactic` + `PEqualNP.Defs` — whole file then compiles in ~25s.
Recipe and details in `wip-3786/NOTES.md`; scratch verifiers
`graph_test2.lean` / `full_test.lean` alongside.
