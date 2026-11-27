#!/usr/bin/env python3
"""Partial matching: notA = union of k diagonal cells (i,i), i<k. s=2k-1 exact (dependence bound).
A = complement. Budget = 2k-1+2n-4. Test A@budget: UNSAT => counterexample."""
import subprocess, sys, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(HERE, "..", "scratch-20959", "venv", "bin", "python")

def solve(n, mask, gates, timeout):
    t0 = time.time()
    try:
        r = subprocess.run([PY, os.path.join(HERE, "exact.py"), str(n), str(mask), str(gates)],
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout + r.stderr
        dt = time.time() - t0
        if "RESULT SAT" in out: return ("SAT", dt)
        if "RESULT UNSAT" in out: return ("UNSAT", dt)
        return ("ERR", dt)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", time.time() - t0)

if __name__ == "__main__":
    n = int(sys.argv[1]); k = int(sys.argv[2])
    full = (1 << (n * n)) - 1
    m_notA = sum(1 << (n * i + i) for i in range(k))
    m_A = full ^ m_notA
    s = 2 * k - 1
    budget = s + 2 * n - 4
    print(f"n={n} k={k} s={s} budget={budget} A_mask={m_A}", flush=True)
    res, dt = solve(n, m_A, budget, 3600)
    print(f"A@{budget}: {res} ({dt:.0f}s)", flush=True)
    if res == "UNSAT":
        print("COUNTEREXAMPLE CANDIDATE", flush=True)
        res2, dt2 = solve(n, m_notA, s, 600)
        print(f"notA@{s} sanity: {res2} ({dt2:.0f}s)", flush=True)
        with open(os.path.join(HERE, "COUNTEREXAMPLE.txt"), "w") as f:
            f.write(f"partial matching n={n} k={k} notA_mask={m_notA} A_mask={m_A} s={s} budget={budget} A@budget=UNSAT notA@s={res2}\n")
