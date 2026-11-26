# L-meta-3786 proof notes

## Status
- Copied L_meta_1602 lines 4-866 into L_meta_3786.lean as namespace
  PEqualNP.Outside.L_meta_3786_aux (contains pairCleanBound + total_from_model
  + full wire infrastructure). Compile check running in background.
- Main theorem still `sorry`. Statement is one huge line (exact skeleton text).

## pairCleanBound (from L_meta_1602)
total_from_model: given abstract S,H,a,b,A with C4-free G, root conditions,
horS/horH/handH (structural), hzero (S(AND)=empty), hjoin (cross pairs are
edges), hpartition (gate counting) => exists vertex cover T with
|E| + |T| <= #gates + 1.
pairCleanBound instantiates with S = supports gs (singleton truth),
H = posRead gs at pairBits, under cleanOn G gs (2-cleanliness: AND gates
true at zero/singleton/pair inputs only when edgeTrue).
- support_and (hzero) uses cleanliness at singletons.
- cross_support (hjoin) uses cleanliness at pairs.
- pos_gate uses cleanliness ONLY to exclude AND[] (empty-input AND) gates.

## Plan to avoid full 2-cleanliness
Use S' = supports gs' where gs' = gs with AND gates replaced by OR[] gates
(constant false). Then:
- hzero for S': definitional (AND wire false in gs').
- horS for S': support_or for gs' (cleanOn gs' vacuous, no AND gates).
- hrS: S'(root) subset S(root) = empty (posRead gs' <= posRead gs pointwise).
- hsmall, hinput: input wires unaffected.
- horH: pos_gate for OR gates needs NO cleanliness.
- handH: pos_gate for AND gates needs no AND[] gates in gs.
- hjoin for S': u in S'(a), v in S'(b) => Adj u v. STILL NEEDS PROOF
  (clean-cross cleanliness). u in S'(a) = a true at singleton u via
  OR-only descent.
- hpartition: gate_partition_count generic in S? CHECK.

## Remaining hard parts
1. No AND[] gates: choose lex-minimal (size, #AND) circuit; AND[] gate
   leads to contradiction via gate replacement (replace mixed AND reader
   by OR-copy, or dead AND[] by OR[]). Needs gate replacement lemma.
2. hjoin for S' (clean-cross): bypass argument with lex-minimality.
   Cases reduce to singleton dirt or clean cross; bypass witnesses y,z;
   neighbors exist; crossing edge. Combinatorics not yet closed.
3. Graph H on Fin 21: L positions 0..8 <-> values [2,4,5,6,7,8,10,11,12],
   R positions 9..20 <-> values [14..25] (b = value-13 in 1..12).
   Edge iff (a+b)%13 in {0,1,3,9}. |E|=36, C4-free, tau>=9 (matching).
4. Statement conversion: A/B quantification <-> graphFun H.

## Key facts
- Circuit = {gates, output}; wires = foldl append; eval = wires.getD output false.
- Monotone2: ops in {and,or}, inputs.length <= 2.
- x2 list in statement: [2,4,5,6,7,8,10,11,12,14,...,25] (Fin 26), 21 elems.
- x3 A B v = if v<13 then (v mod 13 in A) else (v mod 13 in B) [Fin.ofNat].
- x4 a b = (a+b)%13 in [0,1,3,9].

## Update (later session)
- pairCleanBound copy (aux namespace, lines 1-866) compiles CLEAN (verified:
  first full compile had errors only in graph section lines 883+).
- Graph section v1 errors: symm/loopless need `constructor` (Std.Symm/Irrefl);
  diff_unique FALSE as stated (diagonal pairs d1=d2, d3=d4 both give diff 0)
  -> added d1≠d2 hypothesis; omega fails on Fin.val ⟨...⟩ goals -> use `show`;
  commutation fixes in degree_ge; hmatch simp_all timeout -> decide-based.
- Graph fixes v2 + conversion section spliced in (file now 1336 lines).
  Verification compile interrupted by runtime restart at ~42 min, no output
  flushed. Graph fixes v2 + conversion NOT yet verified.
- Environment: Lean compiles take 20-40+ min (Mathlib oleans 6.2GB vs ~6GB
  memory limit -> thrashing, 100GB+ disk reads per compile). Runtime
  restarted once during a compile.
- hjoin (clean-cross cleanliness) remains BLOCKED: bypass argument gets
  stuck at reader analysis (dirty gates between w and readers cause regress;
  key lemma needs cleanliness below, reader cleaning needs control above).
  Full proof needs cleaned-non-edge / TopForm junk theory (repo: L_meta_1499
  1694 lines, L_meta_1528 3495 lines, L_meta_4747 2161 lines) - not feasible
  to replicate here, especially with 20-40 min compile cycles.
- Open question: statement might be false if dirty circuits beat the clean
  bound |E|+tau-1=44 (fleet reductions R_meta_3785_* explore a 43-gate
  construction via 28-gate matrix circuit on 17 inputs, which would beat
  the clean bound 29 for that subgraph). Anneal found no 43-gate circuit.
- File state: L_meta_3786.lean 1336 lines, no double quotes, sorry only in
  main theorem (line 1336). No submit/next/release/beat run. .pnp untouched.

## Build assessment 2026-11-26 14:33 UTC (parent status check)
- File last modified 13:47 UTC (47 min before check); build proc_0b9817232823
  (lean PID 2205) started 14:31 UTC, timeout 3600, output /tmp/compile_out4.txt
  (still 0 bytes - Lean buffers output until errors/complete).
- NOT stuck on decide: after 3 min wall, CPU time only 10s (~6% CPU),
  state S/futex_do_wait, VmRSS ~600MB, VmSize 11GB. read_bytes grew
  2.17GB -> 2.59GB in 30s (~14 MB/s) = still loading/mmap-paging Mathlib
  oleans. Graph-section `decide` calls are all small (Fin 21 / Fin 13,
  lines 900-1165); the expensive 21^4 C4-free decide was already avoided
  via the difference-set argument.
- Root cause of 20-40 min compiles: Mathlib oleans 6.2GB vs ~6GB memory
  limit -> page thrashing (prior compiles read 100GB+ from disk). Any
  `lean` invocation pays this import cost, so splitting the file check
  into smaller pieces does NOT avoid it (each piece re-imports Mathlib).
- Decision: do NOT kill the build; it is progressing (I/O growing).
  Killing/restarting would lose progress and re-pay the same cost.
  Let it run to completion (up to 60 min timeout) to learn whether
  graph-section v2 + conversion section compile.
- Real blocker remains theoretical, not the build: main theorem still
  `sorry` (line 1336); hjoin/cleanliness needs TopForm junk theory
  (L_meta_1499/1528/4747) which is not feasible to replicate here.
  Even a green compile of the current file does not prove the step.

## Static review of graph+conversion sections (2026-11-26, while build runs)
edgeTrue (aux line 195) = ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true - matches
eval_iff_edgeTrue usage. Likely error spots to fix when build output arrives
(do NOT edit .lean until build finishes, to keep error lines meaningful):
1. H21_degree_ge card_bij bullet 1 (~line 1037): `rw [Nat.add_comm (val21 p)
   (val21 q)]; simpa using hp.2` - hp.2 has (val21 p + val21 q)%13, goal after
   rw has swapped sum; simpa likely fails. Fix: drop the rw.
2. H21_degree_ge surjectivity: `interval_cases v` where v is `set`-bound -
   may fail on let-var. Fix if so: `obtain` via omega case split or
   `match` on hv13 with explicit cases.
3. H21_cover_card injOn proof: `simp only [if_pos hpT, if_neg hpT, if_pos hqT,
   if_neg hqT] at heq` - in each by_cases branch one of if_pos/if_neg is
   ill-typed (hpT : p ∈ T cannot feed if_neg). Likely hard error. Fix:
   per-branch `rw [if_pos hpT, if_neg hqT] at heq` etc. (4 branches).
4. eval_iff_edgeTrue ge-case hfin: after `rw [hL, val21_ge hi9']`, goal has
   `(⟨i,hi21⟩ : Fin 21).val - 8`; omega may not unfold Fin.val of mk.
   Fix: add `simp only [Fin.val_mk]` before omega, or use `show`.
5. ofNat13_of_lt/ge: `simp only [Fin.ofNat, Fin.val_mk]` - Fin.ofNat may not
   unfold via equation lemmas. Fix if fails: use `Fin.val_ofNat`-style lemma
   or `Fin.ext` + `simp [Fin.ofNat]` / decide on val via Nat.mod_eq_of_lt.
6. H21 symm/loopless `constructor` - correct only if Mathlib v4.36
   SimpleGraph fields are Std.Symm/Irrefl structures; if they are plain
   Symmetric/Irreflexive Pi types, constructor fails. Fix if so: plain
   `intro v w h` / `intro v h` without constructor.
7. eval_iff_edgeTrue: `simp only [A, ...]` / `simpa [A]` with let-bound A,B -
   may not unfold lets. Fix if fails: `show` with explicit Finset expression
   or `simp only [Finset.mem_image, ...]` after `unfold` via `delta`/`zeta`.
Build status at review time: 4 min elapsed, 14s CPU, 4.3GB read, still in
import loading phase. No output yet.

## Build proc_0b9817232823 TIMED OUT (2026-11-26 ~15:31 UTC)
- 60 min wall, exit 124, user CPU only 23s, sys 4m1s, output file 0 bytes:
  never finished loading imports, no command elaborated. Worse than v1 run
  (which reached graph-section errors). At start (14:33 UTC) memory was
  pressured (5.6Gi used, 2.2Gi available); by 15:32 UTC only 1.1Gi used,
  6.1Gi buff/cache, 6.7Gi available - oleans may now be page-cached.
- `import Mathlib` (skeleton line 1) loads all 6.2GB of Mathlib oleans.
  PEqualNP.Defs modules import only specific Mathlib modules, so narrowing
  imports in a SCRATCH test copy could cut load time a lot (real file keeps
  skeleton imports for submission; checker rules allow Mathlib imports).
- Diagnostic running: trivial file with same imports
  (~/workspace/scratch-3786/trivial_test.lean, proc_a638514d3508,
  timeout 1200) to measure import-load floor with warm cache. If that is
  fast, retry full compile; if slow, switch to narrowed-import scratch
  verification of the graph section only.

## Diagnostic result + narrowed verification (2026-11-26 ~15:40 UTC)
- Trivial-import test (import Mathlib + PEqualNP.Defs, one trivial theorem):
  killed after ~6 min in thrashing regime (8.9GB read > 6.2GB oleans,
  RSS evicted 4.4GB -> 1.8GB, CPU 26s). Full-Mathlib import floor is
  >= 6 min and unstable in this VM; full-file compiles are unreliable
  (one reached graph errors in <40 min, one produced nothing in 60 min).
- Switched to narrowed-import scratch verification:
  ~/workspace/scratch-3786/graph_test2.lean (482 lines) = graph+conversion
  sections (real file lines 865-1333) + edgeTrue def, with imports:
  Mathlib.Combinatorics.SimpleGraph.DegreeSum, Mathlib.Data.Finset.Card,
  Mathlib.Tactic.IntervalCases, Mathlib.Tactic.FinCases, PEqualNP.Defs.
  Running as proc_edaf95afacd8 (timeout 1800, output /tmp/graph_out.txt).
  Smaller working set should avoid thrashing. Real file unchanged.

## RESOLVED: graph+conversion verified, fixes spliced (2026-11-26 ~15:45 UTC)
- Narrowed-import iteration works: graph_test2.lean compiled in 10s, then
  full_test.lean (ENTIRE real file with `import Mathlib` replaced by
  Mathlib.Combinatorics.SimpleGraph.DegreeSum + Mathlib.Data.Finset.Card +
  Mathlib.Tactic + PEqualNP.Defs) compiled EXIT 0 in 25s, 0 errors.
  Only warning: main theorem uses sorry. So aux pairCleanBound copy +
  graph section (H21_c4free, degrees 4/3, H21_edges=36, H21_cover_card
  tau>=9) + conversion (eval_iff_edgeTrue) are all VERIFIED.
- Fixes applied to graph section (now in real file, 1341 lines):
  1. hA/hB precedence bug: `p.val < 9 -> (X in A) <-> ...` parsed as
     `(p.val < 9 -> X in A) <-> ...` (iff binds looser than ->). Added parens.
  2. card_le_card_of_injOn now takes Set.MapsTo/Set.InjOn: added
     Finset.mem_coe to the mem_filter simp calls.
  3. InjOn if-simp: replaced ill-typed simp only [if_pos hpT, if_neg hpT, ...]
     with per-branch `simp only [hpT, hqT, ite_true, ite_false] at heq`
     (rw [if_pos ...] failed: beta redexes in heq).
  4. hL decide -> rfl (decide rejects goals with free proof vars hi21/hi1).
  5. x3fun_lt/ge application: `show x3fun A B (L26[i]'hi1) = x <i,hi21>`
     (defeq by proof irrelevance) before rw, to match getElem proof terms.
  6. ge-case hfin: `show val21 <i,hi21> = i - 8 from val21_ge hi9'`
     (omega cannot unfold Fin.val of mk).
- FAST ITERATION RECIPE for whoever continues: copy real file to scratch,
  replace `import Mathlib` with the 3 narrowed imports above, compile with
  `lean` + LEAN_PATH from `lake env printenv LEAN_PATH` (~25s). Real file
  keeps `import Mathlib` (checker/skeleton form; 60+ min in this VM).
- REMAINING BLOCKER (unchanged, theoretical): main theorem still `sorry`.
  pairCleanBound needs 2-cleanliness (AND gates fire only at edge-pairs
  among 0/1/2-element inputs), false for arbitrary Monotone2 circuits.
  Needs TopForm normalization + junk elimination (repo L_meta_1499 1694
  lines, L_meta_1528 3495, L_meta_4747 2161 with intricate hyps). With
  25s iteration, copying those into the file aux-style is now mechanically
  feasible but is a large adaptation job; not attempted in this session.
- No submit/next/release/beat run. .pnp/ untouched. Real file untracked
  in git (??), 0 double-quote chars, sorry only at line 1341.
