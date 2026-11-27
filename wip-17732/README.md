# WIP: L-meta-17732 partial results (Finch, 2026-11-27)

Released back to the desk 2026-11-27 ~06:47 CST with reason `exhausted`
(inconclusive: no ≤18-gate circuit found, no UNSAT proof either).
Nothing was submitted.

## What was found
- **Best circuit: 21 gates** (beats the desk's record of 24), verified on all
  1024 inputs. See `hand2.py` for the gate list and `sim.py` for the verified
  simulator. Target: f = NOT(OR of the five K4 edge-sets on 5 vertices);
  edge labeling x0=(0,1), x1=(0,2), x2=(0,3), x3=(0,4), x4=(1,2), x5=(1,3),
  x6=(1,4), x7=(2,3), x8=(2,4), x9=(3,4). 3-colourability = K4-freeness here.
- Hand counting suggests pair/triple-factoring structures bottom out at ~20-21;
  18 would need a different structure or internal NOTs. Annealing and SAT CEGIS
  all stalled (best 1006/1024 at monotone-17; CEGIS solves explode at ~80-130
  active rows). No UNSAT — 18 may still be possible.
- **Formalization recipe validated** with a 22-gate test circuit:
  `test22h.lean` (COMPILE_OK with narrowed imports) + generator
  `gen_test22h.py`. Recipe: 32 top-level chunk lemmas (fix 5 bits, cases on
  the other 5 + rfl, each with `set_option maxHeartbeats 4000000 in`), combined
  by term-mode match; FanInTwo via fin_cases+simp; size via decide.
  Plain `decide` over 1024 inputs OOMs — do not retry.
- **21-gate formalization READY** (added 2026-11-27): `formalization21.lean`
  proves `HasCircuitSize 10 f 21` for the actual 21-gate circuit; compiles
  clean with narrowed imports (2m24s, no sorry). Generator:
  `gen_formalization21.py`. If the desk assigns a <=21 rung of this ladder,
  drop it into that skeleton per the instructions at the end of NOTES.md.

Full log in NOTES.md.
