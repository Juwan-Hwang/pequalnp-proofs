#!/usr/bin/env python3
"""Circulant band test: notA(u,v)=[(v-u)%n in S], A=complement.
Construction for notA: OR_u (x_u AND (OR_{v in u+S} y_v)): cost n(w+1)-1, w=|S|.
Test A at budget = construction + 2n - 4. UNSAT => counterexample.
Usage: circ_test.py n w   (S = {0..w-1})"""
import subprocess, sys, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.path.join(HERE, "..", "scratch-20959", "venv", "bin", "python")

def mask_band(n, S):
    m = 0
    for u in range(n):
        for v in range(n):
            if (v - u) % n in S: m |= 1 << (n*u+v)
    return m

def solve(n, mask, gates, timeout):
    t0 = time.time()
    try:
        r = subprocess.run([PY, os.path.join(HERE,"exact.py"), str(n), str(mask), str(gates)],
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout + r.stderr
        dt = time.time()-t0
        if "RESULT SAT" in out: return ("SAT", dt, out)
        if "RESULT UNSAT" in out: return ("UNSAT", dt, out)
        return ("ERR", dt, out[-500:])
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", time.time()-t0, "")

if __name__ == "__main__":
    n = int(sys.argv[1]); w = int(sys.argv[2])
    S = set(range(w))
    full = (1 << (n*n)) - 1
    m_notA = mask_band(n, S); m_A = full ^ m_notA
    constr = n*(w+1)-1
    budget = constr + 2*n - 4
    print(f"n={n} w={w} notA_mask={m_notA} A_mask={m_A} constr(notA)={constr} budget={budget}", flush=True)
    res, dt, out = solve(n, m_A, budget, 3600)
    print(f"A@{budget}: {res} ({dt:.0f}s)", flush=True)
    if res == "UNSAT":
        print("COUNTEREXAMPLE CANDIDATE: cost(A) > budget >= cost(notA)+2n-4", flush=True)
        # verify encoding sanity: notA at construction cost must be SAT
        res2, dt2, out2 = solve(n, m_notA, constr, 600)
        print(f"notA@{constr} sanity: {res2} ({dt2:.0f}s)", flush=True)
        with open(os.path.join(HERE,"COUNTEREXAMPLE.txt"),"w") as f:
            f.write(f"n={n} S={sorted(S)} notA_mask={m_notA} A_mask={m_A} constr(notA)={constr} budget={budget} A@budget=UNSAT notA@constr={res2}\n")
    elif res == "SAT":
        print("consistent (A fits budget)", flush=True)
