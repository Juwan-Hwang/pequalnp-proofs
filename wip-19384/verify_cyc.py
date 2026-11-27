def build(n):
    gates = []
    def add(op, a, b):
        gates.append((op, a, b)); return 2*n + len(gates) - 1
    R = lambda j: n + j
    # R prefixes P[t] = R_0..R_t, t=1..n-2
    P = [R(0)]
    for t in range(1, n-1): P.append(add('OR', P[-1], R(t)))
    # R suffixes S[t] = R_t..R_{n-1}, t=n-2..1
    S = [None]*n
    S[n-1] = R(n-1)
    for t in range(n-2, 0, -1): S[t] = add('OR', R(t), S[t+1])
    # bars: barR_j = P[j-1] OR S[j+1]
    barR = []
    for j in range(n):
        if j == 0: barR.append(S[1])
        elif j == n-1: barR.append(P[n-2])
        else: barR.append(add('OR', P[j-1], S[j+1]))
    # terms L_i AND barR_{i+1 mod n}
    terms = [add('AND', i, barR[(i+1) % n]) for i in range(n)]
    out = terms[0]
    for t in terms[1:]: out = add('OR', out, t)
    return gates, out

def sim(n, gates, out, u, v):
    w = [i == u for i in range(n)] + [j == v for j in range(n)]
    for (op, a, b) in gates: w.append((w[a] and w[b]) if op=='AND' else (w[a] or w[b]))
    return w[out]

for n in range(3, 9):
    gates, out = build(n)
    ok = all(sim(n, gates, out, u, v) == (v != (u+1) % n) for u in range(n) for v in range(n))
    print(f"n={n}: gates={len(gates)} (budget s+2n-4 = {(2*n-1)+(2*n-4)}) correct: {ok}")
