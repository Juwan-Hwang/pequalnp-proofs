"""Hand construction v2: x0-split, 21 gates (target)."""
from sim import check, ncorrect

gates = []
def G(op, *ins):
    gates.append((op, list(ins)))
    return 10 + len(gates) - 1

# A = T0|T1 = tri234 & (star1{4,5,6} | star0{1,2,3})
p1 = G('AND', 7, 8)          # 10
tri = G('AND', p1, 9)        # 11
p2 = G('AND', 4, 5)          # 12
s1 = G('AND', p2, 6)         # 13
p3 = G('AND', 1, 2)          # 14
s0 = G('AND', p3, 3)         # 15
o1 = G('OR', s1, s0)         # 16
A = G('AND', tri, o1)        # 17

# B = T2'|T3' = {3,6} & ({2,5,9} | {1,4,8})
p4 = G('AND', 3, 6)          # 18
p5 = G('AND', 2, 5)          # 19
s3 = G('AND', p5, 9)         # 20
p6 = G('AND', 1, 4)          # 21
s2 = G('AND', p6, 8)         # 22
o2 = G('OR', s3, s2)         # 23
B = G('AND', p4, o2)         # 24

# T4' = {1,2,4,5,7} = p3 & p2 & x7
t = G('AND', p3, p2)         # 25
T4p = G('AND', t, 7)         # 26

C = G('OR', B, T4p)          # 27
D = G('AND', 0, C)           # 28
g = G('OR', A, D)            # 29
f = G('NOT', g)              # 30

print(f"gates: {len(gates)}")
for j, gt in enumerate(gates):
    print(f"  gate {j} -> wire {10+j}: {gt}")
print("correct rows:", ncorrect(gates, f), "/ 1024")
print("check:", "PASS" if check(gates, f, verbose=True) else "FAIL")
