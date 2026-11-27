"""General CNF encoding (pysat) for a fan-in-2 AND/OR circuit for an n x n mask,
correct on the n*n one-a-side inputs. Relaxed normalizations (complete for <=NG
existence for non-constant targets whose function differs from every input wire):
output = last gate, every gate read by a later gate, gates read two earlier wires
(repetition allowed, simulating copies).

Usage: exact.py <n> <mask> <ngates> [solver]
Mask bit (n*u+v) = A(u,v).
"""
import sys
from pysat.solvers import Glucose3, Cadical153

N = int(sys.argv[1])
MASK = int(sys.argv[2])
NG = int(sys.argv[3])
SOLVER = sys.argv[4] if len(sys.argv) > 4 else "cadical"
NIN = 2 * N
NW = NIN + NG
INPUTS = [(u, v) for u in range(N) for v in range(N)]
NT = len(INPUTS)

def A(u, v):
    return bool((MASK >> (N * u + v)) & 1)

print(f"n={N} mask={MASK} gates={NG} solver={SOLVER}", flush=True)
for u in range(N):
    print(u, [int(A(u, v)) for v in range(N)], flush=True)

nextid = [1]
def newvar():
    i = nextid[0]
    nextid[0] += 1
    return i

op = [newvar() for _ in range(NG)]  # True = AND
s1 = [[newvar() for _ in range(NIN + j)] for j in range(NG)]
s2 = [[newvar() for _ in range(NIN + j)] for j in range(NG)]
val = {}
for t in range(NT):
    for j in range(NG):
        val[(t, NIN + j)] = newvar()
x = {(t, j): newvar() for t in range(NT) for j in range(NG)}
y = {(t, j): newvar() for t in range(NT) for j in range(NG)}

def input_const(t, i):
    u, v = INPUTS[t]
    return (i == u) if i < N else (i - N == v)

clauses = []

def onehot(vs):
    clauses.append(list(vs))
    for a in range(len(vs)):
        for b in range(a + 1, len(vs)):
            clauses.append([-vs[a], -vs[b]])

for j in range(NG):
    onehot(s1[j])
    onehot(s2[j])
    for i1 in range(NIN + j):
        for i2 in range(NIN + j):
            if i1 > i2:
                clauses.append([-s1[j][i1], -s2[j][i2]])

for t in range(NT):
    for j in range(NG):
        for i in range(NIN + j):
            for sel, vv in ((s1[j][i], x[(t, j)]), (s2[j][i], y[(t, j)])):
                if i < NIN:
                    c = input_const(t, i)
                    clauses.append([-sel, vv] if c else [-sel, -vv])
                else:
                    w = val[(t, i)]
                    clauses.append([-sel, -vv, w])
                    clauses.append([-sel, vv, -w])
        o, xv, yv, ov = op[j], x[(t, j)], y[(t, j)], val[(t, NIN + j)]
        clauses.append([-o, -ov, xv])
        clauses.append([-o, -ov, yv])
        clauses.append([-o, ov, -xv, -yv])
        clauses.append([o, ov, -xv])
        clauses.append([o, ov, -yv])
        clauses.append([o, -ov, xv, yv])

# output = last gate wire
for t, (u, v) in enumerate(INPUTS):
    clauses.append([val[(t, NW - 1)]] if A(u, v) else [-val[(t, NW - 1)]])

# every gate except last is read by some later gate
for j in range(NG - 1):
    w = NIN + j
    readers = []
    for k in range(j + 1, NG):
        readers.append(s1[k][w])
        readers.append(s2[k][w])
    clauses.append(readers)

print(f"vars={nextid[0]-1} clauses={len(clauses)}", flush=True)
print("solving...", flush=True)
Solver = Cadical153 if SOLVER == "cadical" else Glucose3
with Solver(bootstrap_with=clauses) as s:
    r = s.solve()
    print("result:", "SAT" if r else "UNSAT", flush=True)
    if r:
        mset = set(s.get_model())
        def istrue(v):
            return v in mset
        gates = []
        for j in range(NG):
            i1 = next(i for i in range(NIN + j) if istrue(s1[j][i]))
            i2 = next(i for i in range(NIN + j) if istrue(s2[j][i]))
            gates.append(("AND" if istrue(op[j]) else "OR", i1, i2))
        o = NW - 1
        for j, g in enumerate(gates):
            print(f"  gate {j} -> wire {NIN+j}: {g}", flush=True)
        print("output wire:", o, flush=True)

        def simulate(u, v):
            w = [i == u for i in range(N)] + [jj == v for jj in range(N)]
            for (o_, a, b) in gates:
                w.append((w[a] and w[b]) if o_ == "AND" else (w[a] or w[b]))
            return w[o]
        ok = all(simulate(u, v) == A(u, v) for u in range(N) for v in range(N))
        print(f"independent verification on {NT} inputs:", "PASS" if ok else "FAIL", flush=True)
        with open(f"circuit_n{N}_mask{MASK}_g{NG}.txt", "w") as f:
            for j, g in enumerate(gates):
                f.write(f"{j} {g[0]} {g[1]} {g[2]}\n")
            f.write(f"out {o}\n")
        print("wrote circuit file", flush=True)
