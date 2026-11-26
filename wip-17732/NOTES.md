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
