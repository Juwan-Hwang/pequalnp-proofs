"""Target function and circuit simulation for L-meta-17732.

Target (from Lean statement):
f(x) = NOT( T1 or T2 or T3 or T4 or T5 ) where
  T1 = x4&x5&x6&x7&x8&x9
  T2 = x0&x2&x3&x5&x6&x9
  T3 = x0&x1&x3&x4&x6&x8
  T4 = x0&x1&x2&x4&x5&x7
  T5 = x1&x2&x3&x7&x8&x9
Input n in 0..1023: bit i of n is x_i (matches Lean cross-check).
"""
TERMS = [
    (4, 5, 6, 7, 8, 9),
    (0, 2, 3, 5, 6, 9),
    (0, 1, 3, 4, 6, 8),
    (0, 1, 2, 4, 5, 7),
    (1, 2, 3, 7, 8, 9),
]
NIN = 10
NROWS = 1024

def target_bits(n):
    x = [(n >> i) & 1 for i in range(NIN)]
    g = any(all(x[e] for e in t) for t in TERMS)
    return 0 if g else 1

# Truth tables as Python ints: bit n of the int = value on input n.
INPUT_TT = []
for i in range(NIN):
    tt = 0
    for n in range(NROWS):
        if (n >> i) & 1:
            tt |= 1 << n
    INPUT_TT.append(tt)

TARGET_TT = 0
for n in range(NROWS):
    if target_bits(n):
        TARGET_TT |= 1 << n

FULL = (1 << NROWS) - 1

def eval_circuit_tt(gates, out):
    """gates: list of (op, [ins...]) with op in AND/OR/NOT, Lean semantics:
    AND of [] = True, OR of [] = False, NOT reads first input (missing=False),
    missing wire reads False. Returns truth table int of output wire."""
    wires = list(INPUT_TT)
    for op, ins in gates:
        vals = [wires[i] if i < len(wires) else 0 for i in ins]
        if op == 'AND':
            v = FULL
            for a in vals:
                v &= a
        elif op == 'OR':
            v = 0
            for a in vals:
                v |= a
        elif op == 'NOT':
            v = FULL ^ (vals[0] if vals else 0)
        else:
            raise ValueError(op)
        wires.append(v)
    return wires[out] if out < len(wires) else 0

def check(gates, out, verbose=False):
    tt = eval_circuit_tt(gates, out)
    diff = tt ^ TARGET_TT
    ok = diff == 0
    if verbose and not ok:
        bad = [n for n in range(NROWS) if (diff >> n) & 1]
        print(f"  mismatches: {len(bad)} (first few: {bad[:10]})")
    return ok

def ncorrect(gates, out):
    tt = eval_circuit_tt(gates, out)
    return NROWS - bin(tt ^ TARGET_TT).count('1')

if __name__ == '__main__':
    cnt = bin(TARGET_TT).count('1')
    csum = sum(n + 1 for n in range(NROWS) if (TARGET_TT >> n) & 1)
    print(f"true count: {cnt} (Lean: 958)")
    print(f"checksum:   {csum} (Lean: 472561)")
    # Verify K4-free characterization with edge labeling:
    # x0=(0,1) x1=(0,2) x2=(0,3) x3=(0,4) x4=(1,2) x5=(1,3) x6=(1,4) x7=(2,3) x8=(2,4) x9=(3,4)
    edges = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
    import itertools
    def has_k4(n):
        present = {edges[i] for i in range(10) if (n >> i) & 1}
        for S in itertools.combinations(range(5), 4):
            if all(tuple(sorted(p)) in present for p in itertools.combinations(S, 2)):
                return True
        return False
    bad = [n for n in range(NROWS) if target_bits(n) == (1 if has_k4(n) else 0)]
    print(f"K4-free characterization mismatches: {len(bad)}")
    # Also verify 3-colourability directly by brute force over colourings.
    def three_colourable(n):
        present = [edges[i] for i in range(10) if (n >> i) & 1]
        for col in itertools.product(range(3), repeat=5):
            if all(col[a] != col[b] for a, b in present):
                return True
        return False
    bad2 = [n for n in range(NROWS) if target_bits(n) != (1 if three_colourable(n) else 0)]
    print(f"3-colourability characterization mismatches: {len(bad2)}")
