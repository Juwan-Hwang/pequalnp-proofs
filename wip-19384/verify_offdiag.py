import sys
def build(n):
    # wires 0..n-1 = L, n..2n-1 = R. gates list of (op, a, b), wire index = 2n + gate idx
    gates = []
    def add(op, a, b):
        gates.append((op, a, b))
        return 2*n + len(gates) - 1
    # crosses c_i = L_i OR R_i
    c = [add('OR', i, n+i) for i in range(n)]
    # prefixes P_t = c_0..c_t for t=1..n-2
    P = [c[0]]
    for t in range(1, n-1):
        P.append(add('OR', P[-1], c[t]))
    # ANDs: c_i AND P_{i-1} for i=1..n-1
    ands = [add('AND', c[i], P[i-1]) for i in range(1, n)]
    # OR them
    out = ands[0]
    for a in ands[1:]:
        out = add('OR', out, a)
    return gates, out

def simulate(n, gates, out, u, v):
    w = [i == u for i in range(n)] + [j == v for j in range(n)]
    for (op, a, b) in gates:
        w.append((w[a] and w[b]) if op == 'AND' else (w[a] or w[b]))
    return w[out]

for n in range(3, 9):
    gates, out = build(n)
    ok = all(simulate(n, gates, out, u, v) == (u != v) for u in range(n) for v in range(n))
    print(f"n={n}: gates={len(gates)} (4n-5={4*n-5}) offdiag correct: {ok}")
