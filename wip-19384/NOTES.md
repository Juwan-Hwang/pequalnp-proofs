# L-meta-19384 notes

Statement: forall n s A, 3 <= n -> RepSizeAtMost (complement A) s -> RepSizeAtMost A (s + (2n-4)).

## Definitions
- Circuit: gates list + output wire index. Gate j produces wire (input length)+j.
- Wires 0..len-1 = inputs; nonexistent wire reads false.
- Monotone2: every gate op in {and, or}, inputs.length <= 2.
- Represents A C: for all u v, C.eval (oneEach u v) = A u v. oneEach u v: length n+m list,
  left part has true exactly at u, right part true exactly at v.
- RepSizeAtMost A s: exists C, Monotone2 C and size <= s and Represents A C.

## Repo search (2026-11-27, second prover)
- No existing complementation/dual transformation lemma for RepSizeAtMost in Defs/ or Outside/.
- L_lib_370: restriction lemma (subgraph via injective maps doesn't increase repSize) + `run` lemma
  for running gates under wire relabeling. Useful machinery if induction on n is used.
- L_meta_19123/19155: missing-cell graph has repSize exactly 2n-3 (tight family: cost(notA)=1).

## Math analysis
- Plain dualization (swap AND/OR, complement inputs) needs all input complements
  L_i = OR_{j!=i} x_j, R_j similarly. Cost via prefix/suffix: 3n-6 per side, 6n-12 total >> 2n-4.
  At n=3 all 6 complements need >= 6 gates > budget 2. So dualization is NOT the construction.
- Rectangle extraction also loses too much (offdiag: circuit 4n-5 vs depth-2 rectangle cost ~n^2).
- Perm construction (previous prover, verify_perm.py): for notA = OR_i (x_i AND y_{pi(i)}),
  A computed in 4n-5 gates: crosses c_i = x_i OR y_{pi(i)}, prefixes P, A = OR_{i>=1}(c_i AND P_{i-1})
  = [>=2 crosses true]. Works because rectangles partition both sides. Gap = (4n-5)-(2n-1) = 2n-4 tight.
- Induction on n (peel row/col) fails naively: peeled row function is an arbitrary subset costing up to n-2.
- Induction on circuit structure fails naively: complementing both children pays 2n-4 twice.

## Computational plan
- exact.py verified (diag4 UNSAT@6 SAT@7, independent verification PASS).
- gap_search.py: exact costs at n=5 for families + refutation test (UNSAT at cost(notA)+2n-4).
- Random-circuit search planned: random C (size s) for notA, test A at s+2n-4 gates; UNSAT = counterexample.

## Status
- Running gap_search.py offdiag (n=5): cost(diag5) search in progress (UNSAT@8 slow).

## Update 2026-11-27 evening (prover 2)
- rect_search.py (n=5, random rectangle unions): 20+ trials, all SAT@budget, no counterexample.
- circ_test.py running: n=6, band w=2: constr(notA)=17, budget=25, A@25 solving.
  Best known A constructions give 29 (row decomp) / ~32 (crosses) > 25, so UNSAT would refute.
- P-LEFT CLAIM IS FALSE: notA = single cell (s=1), A = complement of cell.
  Any P-left circuit for A depends on 2n-1 inputs (all x, all y_v v!=j) => >=2n-2 gates
  (size >= #inputs depended on - 1), but P-left budget is s+2n-4 = 2n-3. So P-left/P-right
  strengthenings are dead. Main claim still tight-true here: A = L_i OR R_j, 2n-3 gates.
- Full-row peel works for main claim only with gating (alpha=OR of R^c x's): total
  s+2|R^c|+m-4, fits budget iff 2|R^c|<=n. Not general.
- Crosses+adder idea: A = [sum d_u > sum C_u], d_u=x_u OR C_u, C_u=row ORs of notA.
  Cost ~ orCost(row sets)+O(n). Unclear if orCost(row sets) <= cost(notA)+O(n); random
  strip example suggests ratio up to ~2. Not proven either way.
- Construction still not found. Waiting on circ6w2 (possible counterexample).

## Construction analysis (prover 2, continued)
- Gate-dual crosses: for depth-2 C (OR of ANDs of row/col ORs), duals of AND gates
  are rectangle crosses r_k OR c_k; #crosses = deg_R(u)+deg_C(v)-notA(u,v) (disjoint rects).
  A = [#crosses = deg_R+deg_C]. Works iff degrees constant (perm: (1,1); band w: (1,w)).
  Fails for cell (degrees not constant) — matches direct check.
- Threshold [#crosses >= deg_R+deg_C] as monotone threshold of 3K bits: sorting network
  O(K log^2 K) gates > 2n-4 budget; DP O(K^2). Only small constant thresholds (2,3) feasible.
- CNF construction: A = AND_k (L_{U_k} OR R_{V_k}), cost orCost(complements)+2K-1.
  Fails for diag (8n-13 vs budget 4n-5); crosses works for diag. Neither dominates.
- Row-partition decomposition: every wire of C is a union of <=n rectangles with disjoint
  row sets (refinement by row sets from singletons/[n]: atoms <= |L_g|+1 per gate).
  So K<=n rectangles exist, but orCost of col sets not bounded by s+O(n) (gate-restriction
  counting gives n*s worst case; intrinsic orCost(row sets) vs cost(notA) unresolved).
- Band w=2, n=6: crosses total = 6+6+19 = 31 > budget 25; row decomp 29 > 25.
  If A@25 UNSAT => statement FALSE. circ6w2 running.

## Band results (prover 2)
- n=6,w=2: A has 24-gate circuit (row decomp, pair-OR sharing: 6 pairs + 7 h-ORs + 6 AND + 5 OR),
  verified by simulation. Budget was 25 => CONSISTENT (gap <= 7). circ6w2 SAT solve killed (was >9min).
  Lesson: exact.py SAT instances at n=6/25 gates can be very slow to satisfy; hand constructions beat it.
- n=7,w=2: constr(notA)=20, budget=30. Best A constructions: row decomp 34 (orCost intervals=21),
  crosses 38, L_u&L_{u+1} trick 35. circ7w2 A@30 running in background. UNSAT => counterexample
  (cost(A)>=31 > 20+10 >= cost(notA)+2n-4). SAT => consistent.
- Relative-invariant peel approach (gamma <= [ambient col full], delta <= [local row full]):
  row peels work, col peels need lonely-cell condition, hard case (diag-like) still stuck.
  P-left(+1) (budget s+n+m-3) not refuted by cell example; main claim follows from P-left(+1)
  when R or Cc nonempty. Hard case R=Cc=empty remains the crux for any proof.

## Border decomposition (KEY partial construction)
Rectangular claim: cost(A) <= cost(notA) + n + m - 4, with invariant
gamma(v)=A-circuit(0,e_v) <= [notA col v empty], delta(u) <= [notA row u empty].
- BORDER: S_r = rows with notA nonempty, S_c = cols with notA nonempty.
  A = alpha OR beta OR A'_emb, alpha=OR_{u notin S_r} x_u, beta=OR_{v notin S_c} y_v,
  A' = A|_{S_r x S_c} (IH: <= s+|S_r|+|S_c|-4). Garbage killed by alpha/beta=1 on border.
  Total = s+n+m-4 EXACTLY. Works whenever notA has an empty row or column.
  Invariant maintained (gamma = beta OR gamma' <= [notA col empty]).
- Full notA row u0 with NO lonely columns (no v with notA(·,v)={u0}): A = A'_emb (gamma=0 by invariant).
- Duplicate A rows/cols: wire substitution, +1 gate. Invariant maintained.
- Partial matching (notA = k cells): border + subgrid crosses = 2n+k-3 <= budget for k>=2. CONSISTENT.
- HARD CASE remaining: notA no empty rows/cols; every full row has lonely col; A rows/cols distinct.
  Band w=2 (n=7) is hard case: no lonely cells (min degree 2), no full/empty rows/cols.
  All known constructions for band7w2 A exceed budget 30 (row decomp 34, crosses 38).
  circ7w2 A@30 running: UNSAT => statement FALSE.
