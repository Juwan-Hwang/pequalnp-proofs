def build(n, pi):
    gates = []
    def add(op, a, b):
        gates.append((op, a, b)); return 2*n + len(gates) - 1
    d = [add('OR', i, n + pi[i]) for i in range(n)]  # shifted crosses
    P = [d[0]]
    for t in range(1, n-1): P.append(add('OR', P[-1], d[t]))
    ands = [add('AND', d[i], P[i-1]) for i in range(1, n)]
    out = ands[0]
    for a in ands[1:]: out = add('OR', out, a)
    return gates, out

def sim(n, gates, out, u, v):
    w = [i == u for i in range(n)] + [j == v for j in range(n)]
    for (op, a, b) in gates: w.append((w[a] and w[b]) if op=='AND' else (w[a] or w[b]))
    return w[out]

import random
random.seed(1)
for n in range(3, 10):
    for trial in range(3):
        pi = list(range(n)); random.shuffle(pi)
        gates, out = build(n, pi)
        ok = all(sim(n, gates, out, u, v) == (v != pi[u]) for u in range(n) for v in range(n))
        print(f"n={n} pi={pi}: gates={len(gates)} (4n-5={4*n-5}) correct: {ok}")
