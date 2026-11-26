import itertools

header = """import PEqualNP.Defs.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ22 : Circuit :=
  ⟨[⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [10, 9]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [12, 6]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.and, [14, 3]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.and, [11, 16]⟩,
    ⟨GateOp.and, [0, 3]⟩,
    ⟨GateOp.and, [18, 6]⟩,
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.and, [20, 9]⟩,
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [22, 8]⟩,
    ⟨GateOp.or, [21, 23]⟩,
    ⟨GateOp.and, [19, 24]⟩,
    ⟨GateOp.and, [22, 0]⟩,
    ⟨GateOp.and, [20, 7]⟩,
    ⟨GateOp.and, [26, 27]⟩,
    ⟨GateOp.or, [17, 25]⟩,
    ⟨GateOp.or, [29, 28]⟩,
    ⟨GateOp.not, [30]⟩], 31⟩

"""

def b(v):
    return "true" if v else "false"

lines = [header]
names = []
for combo in itertools.product([False, True], repeat=5):
    a, c_b, c, d, e = combo
    nm = "chunk" + "".join("1" if v else "0" for v in combo)
    names.append(nm)
    A, B, C, D, E = b(a), b(c_b), b(c), b(d), b(e)
    lines.append(f"""set_option maxHeartbeats 4000000 in
theorem {nm} : ∀ f g h i j : Bool,
    circ22.eval [{A}, {B}, {C}, {D}, {E}, f, g, h, i, j] =
    !(({E} && f && g && h && i && j) || ({A} && {C} && {D} && f && g && j) ||
      ({A} && {B} && {D} && {E} && g && i) || ({A} && {B} && {C} && {E} && f && h) ||
      ({B} && {C} && {D} && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

""")

match_arms = []
for combo in itertools.product([False, True], repeat=5):
    nm = "chunk" + "".join("1" if v else "0" for v in combo)
    pat = ", ".join(b(v) for v in combo)
    match_arms.append(f"    | {pat} => {nm} f g h i j")
lines.append("""set_option maxHeartbeats 4000000 in
theorem key22 : ∀ a b c d e f g h i j : Bool,
    circ22.eval [a, b, c, d, e, f, g, h, i, j] =
    !((e && f && g && h && i && j) || (a && c && d && f && g && j) ||
      (a && b && d && e && g && i) || (a && b && c && e && f && h) ||
      (b && c && d && h && i && j)) :=
  fun a b c d e f g h i j =>
    match a, b, c, d, e with
""" + "\n".join(match_arms) + "\n\n")

lines.append("""set_option maxHeartbeats 4000000 in
theorem test22h :
    PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun x : Fin 10 → Bool => !((x 4 && x 5 && x 6 && x 7 && x 8 && x 9) ||
        (x 0 && x 2 && x 3 && x 5 && x 6 && x 9) ||
        (x 0 && x 1 && x 3 && x 4 && x 6 && x 8) ||
        (x 0 && x 1 && x 2 && x 4 && x 5 && x 7) ||
        (x 1 && x 2 && x 3 && x 7 && x 8 && x 9))) 22 := by
  refine ⟨circ22, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · intro x
    have hofn : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
    rw [hofn]
    exact key22 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
""")

with open("test22h.lean", "w") as fh:
    fh.write("".join(lines))
print("wrote test22h.lean")
