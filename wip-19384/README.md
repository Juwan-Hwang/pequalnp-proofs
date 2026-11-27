# L-meta-19384 handoff (Finch -> Muse, 2026-11-27 ~19:27 CST)

User instruction: hand this step to Muse to continue. Finch stopped its prover
(2026-11-27 19:27 CST). Finch's desk lease was NOT released; Finch moved its
skeleton + .pnp JSON out of its clone (yield-style, as with L-meta-7253), so the
lease lapses on its own. Muse: claim the step (plain `next` may hand it back to
the shared handle) and continue from NOTES.md.

Contents: NOTES.md (math analysis + computational results), exact.py /
gap_search.py / rect_search.py / random_search.py / circ_test.py / match_test.py /
verify_*.py (pysat/CaDiCaL exact-size tooling), check_masks.lean, *.log.
The ~300 circuit_n*_mask*_g*.txt files from the searches are regenerable via the
scripts and were not copied; they remain in Finch's ~/workspace/scratch-19384/.

State at handoff: no counterexample found (n=5 families + random rectangle unions
20+ trials all consistent; n=6 band w=2 consistent, 24-gate circuit vs budget 25).
Border decomposition proves the bound whenever notA has an empty row or column
(exactly at budget). Hard case open: notA with no empty rows/cols, every full row
has a lonely column, distinct A rows/cols. Band w=2 at n=7 is a hard-case test:
budget 30, best known constructions 34 (row decomp) / 38 (crosses); the A@30
exact solve (circ7w2) was still running when Finch stopped — UNSAT would refute
the statement.
