# L-meta-17732 notes (Finch prover, 2026-11-27)

## Statement
HasCircuitSize 10 f 18, f(x) = NOT(∨ of five 6-ANDs). The five terms are the
K4 edge-sets on 5 vertices (edge labeling x0=(0,1),x1=(0,2),x2=(0,3),x3=(0,4),
x4=(1,2),x5=(1,3),x6=(1,4),x7=(2,3),x8=(2,4),x9=(3,4)). f = 3-colourability
= K4-freeness. Verified: Python sim.py matches Lean #eval (958 true rows,
checksum 472561); K4-free and 3-colourable characterizations match on all rows.

## Hand constructions (verified by sim.py)
- 22 gates (hand1.py): pair-group K4 terms, factor shared triangle, share pairs.
- 21 gates (hand2.py): x0-split: g = (T0|T1) | (x0 & (T2'|T3'|T4')) with
  triangle factoring; 6 pair-ANDs + 5 triples + combines + NOT. Verified PASS.
  Desk record is 24, so 21 already beats it — but the step needs <=18.

## Search results so far (all stall ~1000-1006/1024 at 17-18 gates)
- Annealing monotone 17 (anneal2.py): best 1006/1024 (18 wrong rows, missing
  K4s on {0,1,2,3},{0,1,2,4} in sparse configs). Stalls.
- Annealing general 18 (anneal3.py): best 1001/1024, no improvement in 300s.
- SAT CEGIS monotone 17 (search_sat*.py): stalls at ~94 active rows across
  variants (plain, batched, lex breaks, MapleCM). Full-instance (all 1024
  rows, lex breaks) running: sat_full_mono17.log.
- SAT CEGIS general 18: stalls at ~127 rows.
- SAT repair (repair_sat.py): freeing <=6 gates of annealed/PlanA candidates
  => UNSAT fast; freeing >=8 => stalls at ~100 rows.
- Lex-order symmetry break (search_sat3.py): gates sorted by (in2,in1,op);
  valid by greedy-ordering argument. Note: gate0 S5-break conflicts with lex
  order in disjoint case — dropped for monotone.

## Lean formalization status — PATH VALIDATED (test22h.lean, COMPILE_OK 2m20s)
- `by decide` on ∀ x : Fin 10 → Bool: maxRecDepth / OOM. 1024-goal cases+rfl:
  OOM. decide-after-cases (Fintype): OOM. 32 haves in one declaration:
  cumulative heartbeats exceeded at combination.
- WORKING: 32 top-level chunk lemmas (fix 5 bits, `cases` on other 5 + `rfl`,
  each with `set_option maxHeartbeats 4000000 in`), combined by term-mode
  `match a, b, c, d, e with` (32 arms), `List.ofFn x = [x 0..x 9]` by `rfl`.
  Generator: gen_test22h.py. FanInTwo via `fin_cases hg <;> simp`, size via
  `decide`. In real file: chunks+key+circuit inside
  `namespace PEqualNP.Outside.L_meta_17732` block, theorem last, full name.
- File rules: set_option limits as `set_option X N in` above the declaration;
  no comments with banned words; no double quotes.

## Final status (2026-11-27, after service restart)
- Full-instance monotone-17 SAT: TIMEOUT at 1500s (no result).
- CEGIS monotone-16 (batch 32): reached it4 (124 rows, wrong 120) at 220s,
  then killed by service restart. Same ~95-row wall.
- CEGIS general-18 (batch 8): reached it8 (86 rows, wrong 134) at 698s;
  solves explode ~80-95 rows. Killed (stalled).
- Focused annealing (anneal4.py, 1200s): no improvement over greedy seed
  1002/1024 at 18 gates.
- NO <=18 circuit found. NO UNSAT proof. Best verified = 21 gates (hand2.py,
  re-verified 1024/1024 PASS). Formalization path validated (test22h.lean).
- Skeleton file untouched (still sorry). Nothing submitted/released.

## 21-gate formalization — READY (formalization21.lean, compiles clean)
Prepared 2026-11-27 (prep only; no lease held, nothing submitted). The actual
21-gate circuit from hand2.py is now fully formalized:
- Generator: gen_formalization21.py (asserts the gate list against sim.py on
  all 1024 inputs before emitting; regenerates formalization21.lean).
- formalization21.lean (369 lines): `circ21` + 32 chunk lemmas + `key21`
  inside `namespace PEqualNP.Outside.L_meta_17732`, then the theorem
  `PEqualNP.Outside.L_meta_17732` with the skeleton's exact statement but
  bound 21 instead of 18 (verified character-identical modulo the bound).
  No sorry, no double quotes, no # commands; set_option only as
  `set_option maxHeartbeats 4000000 in`.
- Verified: compiles clean with narrowed imports (`import
  PEqualNP.Defs.MetaComplexity`) via `lean` with LEAN_PATH from
  `lake env printenv LEAN_PATH` in ~/workspace/pequalnp-proofs/lean —
  exit 0, empty log, 2m24s. Log: compile21.log.

### How to drop into a real <=21 skeleton
1. Take the assigned step's skeleton file (it will have `import Mathlib`,
   `import PEqualNP.Defs`, and `theorem PEqualNP.Outside.L_meta_<N> :
   (... HasCircuitSize 10 f <bound>) := by sorry`).
2. Replace the skeleton's theorem+`sorry` with everything in
   formalization21.lean AFTER its first import line (i.e. from
   `namespace PEqualNP.Outside.L_meta_17732` to the end). Keep the
   skeleton's two imports; delete formalization21.lean's
   `import PEqualNP.Defs.MetaComplexity` line.
3. If the assigned step is not L-meta-17732, rename `L_meta_17732` to the
   step's own name everywhere it appears (namespace line, `end` line,
   theorem name, and the two qualified references
   `PEqualNP.Outside.L_meta_17732.circ21` / `.key21` in the proof).
   If the skeleton's bound is 22/23/24 instead of 21, change the `21` in
   the theorem statement to match — the proof still works (size is proved
   by `decide` against the actual gate count 21, and 21 <= bound).
   If the bound is < 21, this formalization does not apply.
4. Run `tools/pnp.sh check <step>` then `tools/pnp.sh submit <step>` as usual.
- Expected full-build cost: NOT measured (no lease, prep only). The narrowed
  compile took 2m24s, almost all of it chunk elaboration. The real file's
  `import Mathlib` + `import PEqualNP.Defs` (umbrella) will load far more
  oleans than the narrowed import — expect the check build to take
  substantially longer (plausibly 5-20 min) and watch memory: full-Mathlib
  loads have thrashed in this VM before (~6.2GB oleans vs ~6GB RAM). If
  `pnp.sh check` OOMs, that is an environment limit, not a proof error —
  the proof is verified clean under narrowed imports.
