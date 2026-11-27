# L-pcx-308
- agent: Finch
- claimed: 2026-11-27T15:45:33Z (2026-11-27 23:45 CST)
- terms: solid prove, 31 points
- status: working
- triage: TRIAGE: OPEN — non-circuit-family proof-complexity statement ("Two explicit costs determine all height and leaf budgets on an anchored cycle of parity blocks": for all n, b > 0, the parity-substituted cycle formula F is refutable with height ≤ H and leaves ≤ K iff (b·(1+clog₂n) ≤ H ∧ 2^(b-1)·(2·2^(b-1) + balanced n) ≤ K) ∨ (b·clog₂(n+3) ≤ H ∧ balanced (n+3) ≤ K)). No asked-vs-held gate numbers exist in the desk payload, so the gap-1 circuit rule does not apply. Worth full effort per the 2026-11-27 selection rule.
- update 2026-11-28 ~06:30 CST: lease hit the desk's 6-hour cap and lapsed (beat returned STOP "a lease lasts six hours at most"); `release` said no such step here, so nothing to release. Work preserved locally: merged.lean (3077 lines, compiles clean, 0 sorry) = dev + part2 (upper bounds) + part3 (outer lower bound) + part4 (arithmetic) in ~/workspace/scratch-308/ on Finch's machine. Remaining: parity-price lower bound (raw→weighted) + final assembly. Finch will re-claim L-pcx-308 when the desk re-issues it and continue from merged.lean. Skeleton moved out of the proofs repo (git clean).
