"""Rectangle-union counterexample search for L-meta-19384.

notA = union of K random rectangles (depth-2 cost gives an upper bound s0;
exact cost computed via SAT binary search). Test A at budget = cost(notA)+2n-4.
UNSAT at budget => counterexample.
"""
import subprocess, sys, os, random, time

PY = os.path.expanduser("~/workspace/scratch-20959/venv/bin/python")
EXACT = os.path.expanduser("~/workspace/scratch-19384/exact.py")
CWD = os.path.expanduser("~/workspace/scratch-19384")

def solve(n, mask, ng, timeout=240):
    if ng <= 0:
        return "UNSAT"
    try:
        r = subprocess.run([PY, EXACT, str(n), str(mask), str(ng), "cadical"],
                           capture_output=True, text=True, timeout=timeout, cwd=CWD)
        out = r.stdout
        if "result: SAT" in out:
            assert "PASS" in out, out[-400:]
            return "SAT"
        if "result: UNSAT" in out:
            return "UNSAT"
        return "ERROR"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"

def exact_cost(n, mask, hi, timeout=240):
    lo, hi_ = 1, hi
    if solve(n, mask, hi_, timeout=timeout) != "SAT":
        return None
    while lo < hi_:
        mid = (lo + hi_) // 2
        rm = solve(n, mask, mid, timeout=timeout)
        if rm == "SAT":
            hi_ = mid
        elif rm == "UNSAT":
            lo = mid + 1
        else:
            return None
    return hi_

def is_trivial(n, mask):
    full = (1 << (n * n)) - 1
    if mask == 0 or mask == full:
        return True
    for i in range(n):
        m = sum(1 << (n * u + v) for u in range(n) for v in range(n) if u == i)
        if mask == m:
            return True
        m = sum(1 << (n * u + v) for u in range(n) for v in range(n) if v == i)
        if mask == m:
            return True
    return False

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    rng = random.Random(seed)
    full = (1 << (n * n)) - 1
    for t in range(trials):
        K = rng.choice([2, 3, 3, 4, 4, 5])
        rects = []
        maskN = 0
        s0 = 0
        for _ in range(K):
            ku = rng.choice([1, 1, 2, 2, 3])
            kv = rng.choice([1, 1, 2, 2, 3])
            U = rng.sample(range(n), ku)
            V = rng.sample(range(n), kv)
            rects.append((U, V))
            s0 += ku + kv - 1
            for u in U:
                for v in V:
                    maskN |= 1 << (n * u + v)
        s0 += K - 1  # OR gates joining rectangles (depth-2 upper bound)
        maskA = full ^ maskN
        if is_trivial(n, maskN) or is_trivial(n, maskA):
            continue
        t0 = time.time()
        cN = exact_cost(n, maskN, hi=s0, timeout=180)
        if cN is None:
            print(f"trial {t}: K={K} maskN={maskN} cost(notA) unresolved (s0={s0}), skip", flush=True)
            continue
        budget = cN + 2 * n - 4
        r = solve(n, maskA, budget, timeout=420)
        dt = time.time() - t0
        print(f"trial {t}: K={K} rects={rects} cost(notA)={cN} budget={budget} A@budget={r} ({dt:.0f}s)", flush=True)
        if r == "UNSAT":
            print(f"*** COUNTEREXAMPLE: n={n} A={maskA} notA={maskN} costNotA={cN} budget={budget} rects={rects} ***", flush=True)
            with open(os.path.join(CWD, "COUNTEREXAMPLE.txt"), "a") as f:
                f.write(f"n={n} A={maskA} notA={maskN} costNotA={cN} budget={budget} rects={rects}\n")
            return
    print("done, no counterexample in this batch", flush=True)

if __name__ == "__main__":
    main()
