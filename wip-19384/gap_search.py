"""Exact repSize computation + counterexample search for L-meta-19384.

Statement to test: cost(A) <= cost(not A) + 2n - 4.
Counterexample: A with cost(A) > cost(not A) + 2n - 4.

Uses exact.py (pysat/CaDiCaL) via subprocess with timeouts.
Mask bit (n*u+v) = A(u,v).
"""
import subprocess, sys, os, random, time

PY = os.path.expanduser("~/workspace/scratch-20959/venv/bin/python")
EXACT = os.path.expanduser("~/workspace/scratch-19384/exact.py")
CWD = os.path.expanduser("~/workspace/scratch-19384")

def mask_of(n, f):
    m = 0
    for u in range(n):
        for v in range(n):
            if f(u, v):
                m |= 1 << (n * u + v)
    return m

def complement(n, mask):
    return ((1 << (n * n)) - 1) ^ mask

def solve(n, mask, ng, timeout=300):
    """Returns 'SAT', 'UNSAT', or 'TIMEOUT'."""
    try:
        r = subprocess.run([PY, EXACT, str(n), str(mask), str(ng), "cadical"],
                           capture_output=True, text=True, timeout=timeout, cwd=CWD)
        out = r.stdout
        if "result: SAT" in out:
            assert "independent verification on" in out and "PASS" in out, out[-500:]
            return "SAT"
        if "result: UNSAT" in out:
            return "UNSAT"
        return "ERROR:" + out[-300:] + r.stderr[-300:]
    except subprocess.TimeoutExpired:
        return "TIMEOUT"

def exact_cost(n, mask, lo=0, hi=None, timeout=300, log=print):
    """Find exact cost: smallest ng with SAT. Assumes UNSAT below lo not checked.
    Searches upward from lo. Returns (cost, status) where status in
    {'exact','timeout','sat-only'}; cost is exact if status=='exact'."""
    ng = lo
    while hi is None or ng <= hi:
        t0 = time.time()
        r = solve(n, mask, ng, timeout=timeout)
        log(f"  n={n} mask={mask} gates={ng}: {r} ({time.time()-t0:.1f}s)", flush=True)
        if r == "SAT":
            return ng, "exact"
        if r == "TIMEOUT":
            return ng, "timeout"
        ng += 1
    return None, "exceeded-hi"

def check_gap(n, maskA, name, timeout=300, log=print):
    """Compute exact cost(A) and cost(not A), report gap. Returns gap or None."""
    maskN = complement(n, maskA)
    log(f"== {name}: n={n} A mask={maskA} notA mask={maskN}", flush=True)
    # lower bound for cost(notA): 0; just search up. But to save time, first
    # check the refutation condition directly if we have an upper bound for notA.
    cN, stN = exact_cost(n, maskN, lo=0, timeout=timeout, log=log)
    if stN != "exact":
        log(f"  cost(notA) unresolved ({stN} at {cN})", flush=True)
        return None
    log(f"  cost(notA) = {cN}; budget for A = {cN + 2*n - 4}", flush=True)
    # Refutation test: is cost(A) > cN + 2n - 4? i.e. UNSAT at cN+2n-4.
    budget = cN + 2 * n - 4
    r = solve(n, maskA, budget, timeout=timeout)
    log(f"  A at budget {budget}: {r}", flush=True)
    if r == "UNSAT":
        log(f"  *** COUNTEREXAMPLE: cost(A) > {budget} = cost(notA)+2n-4 ***", flush=True)
        return ("COUNTEREXAMPLE", cN, budget)
    if r == "SAT":
        # find exact cost(A) <= budget by searching down from budget? search up from 0 is wasteful;
        # binary search between 0 and budget using monotonicity (SAT at k => SAT at k+1? 
        # exact.py encoding: <=NG existence is monotone since extra gates can be copies? 
        # The encoding forces every gate read + output=last; padding with AND(w,w) works.)
        lo_, hi_ = 0, budget
        # invariant: SAT at hi_
        while lo_ < hi_:
            mid = (lo_ + hi_) // 2
            rm = solve(n, maskA, mid, timeout=timeout)
            log(f"  A binary search gates={mid}: {rm}", flush=True)
            if rm == "SAT":
                hi_ = mid
            elif rm == "UNSAT":
                lo_ = mid + 1
            else:
                log(f"  unresolved in binary search ({rm})", flush=True)
                return ("consistent-unresolved", cN, budget)
        log(f"  cost(A) = {hi_}, gap = {hi_ - cN} (bound {2*n-4})", flush=True)
        return ("consistent", cN, hi_)
    log(f"  unresolved ({r})", flush=True)
    return None

if __name__ == "__main__":
    n = 5
    fams = {}
    fams["offdiag"] = mask_of(n, lambda u, v: u != v)
    fams["diag"] = mask_of(n, lambda u, v: u == v)
    # circulant band: (v-u) mod n in {2,3}
    fams["band23"] = mask_of(n, lambda u, v: (v - u) % n in (2, 3))
    fams["band34"] = mask_of(n, lambda u, v: (v - u) % n in (3, 4))
    fams["band123"] = mask_of(n, lambda u, v: (v - u) % n in (1, 2, 3))
    # missing k diagonal cells: A = all ones except (i,i) for i<k
    for k in (2, 3, 4):
        fams[f"missdiag{k}"] = mask_of(n, lambda u, v, k=k: not (u == v and u < k))
    # block complement: notA = U x V, |U|=|V|=2
    fams["blockcomp22"] = complement(n, mask_of(n, lambda u, v: u in (0, 1) and v in (0, 1)))
    fams["blockcomp23"] = complement(n, mask_of(n, lambda u, v: u in (0, 1) and v in (0, 1, 2)))
    # notA = two diagonal blocks
    fams["twoblocks"] = complement(n, mask_of(n, lambda u, v: (u in (0,1) and v in (0,1)) or (u in (3,4) and v in (3,4))))
    # notA = first two rows fully
    fams["tworowscomp"] = complement(n, mask_of(n, lambda u, v: u in (0, 1)))
    # notA = cross: row 0 union col 0
    fams["crosscomp"] = complement(n, mask_of(n, lambda u, v: u == 0 or v == 0))
    # A = cross itself
    fams["cross"] = mask_of(n, lambda u, v: u == 0 or v == 0)
    # A = block itself
    fams["block22"] = mask_of(n, lambda u, v: u in (0, 1) and v in (0, 1))

    which = sys.argv[1:] if len(sys.argv) > 1 else list(fams.keys())
    for name in which:
        res = check_gap(n, fams[name], name, timeout=600)
        print(f"RESULT {name}: {res}", flush=True)
