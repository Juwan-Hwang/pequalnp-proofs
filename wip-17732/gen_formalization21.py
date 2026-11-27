"""Generate formalization21.lean: Lean proof that the 21-gate circuit from
hand2.py computes the L-meta-17732 target function (3-colourability of
5-vertex graphs on 10 edge bits), i.e. HasCircuitSize 10 f 21.

Adapted from gen_test22h.py (validated recipe). Asserts with sim.py that the
gate list below is correct on all 1024 inputs before emitting any Lean.
"""
import itertools
import sys

sys.path.insert(0, ".")
from sim import check

# 21-gate circuit from hand2.py. Gate j produces wire 10 + j; output wire 30.
GATES = [
    ("AND", [7, 8]),    # 10
    ("AND", [10, 9]),   # 11
    ("AND", [4, 5]),    # 12
    ("AND", [12, 6]),   # 13
    ("AND", [1, 2]),    # 14
    ("AND", [14, 3]),   # 15
    ("OR", [13, 15]),   # 16
    ("AND", [11, 16]),  # 17
    ("AND", [3, 6]),    # 18
    ("AND", [2, 5]),    # 19
    ("AND", [19, 9]),   # 20
    ("AND", [1, 4]),    # 21
    ("AND", [21, 8]),   # 22
    ("OR", [20, 22]),   # 23
    ("AND", [18, 23]),  # 24
    ("AND", [14, 12]),  # 25
    ("AND", [25, 7]),   # 26
    ("OR", [24, 26]),   # 27
    ("AND", [0, 27]),   # 28
    ("OR", [17, 28]),   # 29
    ("NOT", [29]),      # 30 (output)
]
OUTPUT = 30

assert len(GATES) == 21
assert check(GATES, OUTPUT), "gate list does not compute the target function"
print("sim check: PASS (21 gates, 1024/1024)")

OP_LEAN = {"AND": "GateOp.and", "OR": "GateOp.or", "NOT": "GateOp.not"}

gate_lines = []
for op, ins in GATES:
    ins_s = ", ".join(str(i) for i in ins)
    gate_lines.append(f"⟨{OP_LEAN[op]}, [{ins_s}]⟩")
gates_lean = ",\n    ".join(gate_lines)

header = f"""import PEqualNP.Defs.MetaComplexity

namespace PEqualNP.Outside.L_meta_17732

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ21 : Circuit :=
  ⟨[{gates_lean}], {OUTPUT}⟩

"""

def b(v):
    return "true" if v else "false"

# Target expression in terms of a=x0 b=x1 c=x2 d=x3 e=x4 f=x5 g=x6 h=x7 i=x8 j=x9.
def mk_rhs(a, b_, c, d, e):
    return (f"!(({e} && f && g && h && i && j) || ({a} && {c} && {d} && f && g && j) ||\n"
            f"      ({a} && {b_} && {d} && {e} && g && i) || ({a} && {b_} && {c} && {e} && f && h) ||\n"
            f"      ({b_} && {c} && {d} && h && i && j))")

RHS = mk_rhs("a", "b", "c", "d", "e")

lines = [header]
for combo in itertools.product([False, True], repeat=5):
    a, c_b, c, d, e = combo
    nm = "chunk" + "".join("1" if v else "0" for v in combo)
    A, B, C, D, E = b(a), b(c_b), b(c), b(d), b(e)
    rhs_s = mk_rhs(A, B, C, D, E)
    lines.append(f"""set_option maxHeartbeats 4000000 in
theorem {nm} : ∀ f g h i j : Bool,
    circ21.eval [{A}, {B}, {C}, {D}, {E}, f, g, h, i, j] =
    {rhs_s} := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

""")

match_arms = []
for combo in itertools.product([False, True], repeat=5):
    nm = "chunk" + "".join("1" if v else "0" for v in combo)
    pat = ", ".join(b(v) for v in combo)
    match_arms.append(f"    | {pat} => {nm} f g h i j")
lines.append(f"""set_option maxHeartbeats 4000000 in
theorem key21 : ∀ a b c d e f g h i j : Bool,
    circ21.eval [a, b, c, d, e, f, g, h, i, j] =
    {RHS} :=
  fun a b c d e f g h i j =>
    match a, b, c, d, e with
""" + "\n".join(match_arms) + """

end PEqualNP.Outside.L_meta_17732

""")

lines.append("""theorem PEqualNP.Outside.L_meta_17732 : (PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => !((x 4 && x 5 && x 6 && x 7 && x 8 && x 9) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9) || (x 0 && x 1 && x 3 && x 4 && x 6 && x 8) || (x 0 && x 1 && x 2 && x 4 && x 5 && x 7) || (x 1 && x 2 && x 3 && x 7 && x 8 && x 9))) 21) := by
  refine ⟨PEqualNP.Outside.L_meta_17732.circ21, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · intro x
    have hofn : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
    rw [hofn]
    exact PEqualNP.Outside.L_meta_17732.key21 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
""")

out = "".join(lines)
assert '"' not in out, "double quote in output"
assert "sorry" not in out
with open("formalization21.lean", "w") as fh:
    fh.write(out)
print("wrote formalization21.lean")
