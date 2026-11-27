"""Random-circuit counterexample search for L-meta-19384 at n=5.

Generate a random monotone circuit C of size s (for notA), compute A = complement
of C's function on one-a-side inputs. Compute exact cost(notA) via SAT, then test
A at budget = cost(notA) + 2n - 4. UNSAT at budget => counterexample.
"""
import subprocess, sys, os, random, time

PY = os.path.expanduser("~/workspace/scratch-20959/venv/bin/python")
EXACT = os.path.expanduser("~/workspace/scratch-19384/exact.py")
CWD = os.path.expanduser("~/workspace/scratch-19384")

def solve(n, mask, ng, timeout=180):
    if ng <= 0:
        return "UNSAT"  # caller must ensure target is not an input wire / constant
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

def exact_cost(n, mask, hi, timeout=180):
    """Exact cost given SAT at hi (hi = known upper bound). Binary search.
    Returns cost or None if unresolved. Assumes cost >= 1 (mask not input-wire/const)."""
    lo, hi_ = 1, hi
    # check SAT at hi first
    r = solve(n, mask, hi_, timeout=timeout)
    if r != "SAT":
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

def random_circuit_mask(n, s, rng):
    """Random monotone circuit with s gates on 2n inputs; return mask of its function."""
    NIN = 2 * n
    gates = []
    for j in range(s):
        nw = NIN + j
        a = rng.randrange(nw)
        b = rng.randrange(nw)
        op = rng.choice(["AND", "OR"])
        gates.append((op, a, b))
    out = NIN + s - 1
    mask = 0
    for u in range(n):
        for v in range(n):
            w = [i == u for i in range(n)] + [j == v for j in range(n)]
            for (op, a, b) in gates:
                w.append((w[a] and w[b]) if op == "AND" else (w[a] or w[b]))
            if w[out]:
                mask |= 1 << (n * u + v)
    return mask

def is_trivial(n, mask):
    """True if mask is constant or equals an input wire function (cost 0)."""
    full = (1 << (n * n)) - 1
    if mask == 0 or mask == full:
        return True
    for i in range(n):
        # left wire i: A(u,v) = [u==i]
        m = 0
        for u in range(n):
            for v in range(n):
                if u == i:
                    m |= 1 << (n * u + v)
        if mask == m:
            return True
        # right wire i: A(u,v) = [v==i]
        m = 0
        for u in range(n):
            for v in range(n):
                if v == i:
                    m |= 1 << (n * u + v)
        if mask == m:
            return True
    return False

def main():
    n = 5
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    for t in range(trials):
        s = rng.choice([5, 6, 7, 8, 9, 10])
        maskN = random_circuit_mask(n, s, rng)
        maskA = ((1 << (n * n)) - 1) ^ maskN
        if is_trivial(n, maskN) or is_trivial(n, maskA):
            continue
        t0 = time.time()
        cN = exact_cost(n, maskN, hi=s, timeout=120)
        if cN is None:
            print(f"trial {t}: s={s} maskN={maskN} cost(notA) unresolved, skip", flush=True)
            continue
        budget = cN + 2 * n - 4
        r = solve(n, maskA, budget, timeout=300)
        dt = time.time() - t0
        print(f"trial {t}: s={s} maskN={maskN} cost(notA)={cN} budget={budget} A@budget={r} ({dt:.0f}s)", flush=True)
        if r == "UNSAT":
            print(f"*** COUNTEREXAMPLE FOUND: n={n} A mask={maskA} notA mask={maskN} "
                  f"cost(notA)={cN} cost(A)>{budget} ***", flush=True)
            with open(os.path.join(CWD, "COUNTEREXAMPLE.txt"), "a") as f:
                f.write(f"n={n} A={maskA} notA={maskN} costNotA={cN} budget={budget}\n")
            return
    print("done, no counterexample in this batch", flush=True)

if __name__ == "__main__":
    main()
