import PEqualNP.Defs.MetaComplexity

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

set_option maxHeartbeats 4000000 in
theorem chunk00000 : ∀ f g h i j : Bool,
    circ22.eval [false, false, false, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && false && false && f && g && j) ||
      (false && false && false && false && g && i) || (false && false && false && false && f && h) ||
      (false && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00001 : ∀ f g h i j : Bool,
    circ22.eval [false, false, false, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && false && false && f && g && j) ||
      (false && false && false && true && g && i) || (false && false && false && true && f && h) ||
      (false && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00010 : ∀ f g h i j : Bool,
    circ22.eval [false, false, false, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && false && true && f && g && j) ||
      (false && false && true && false && g && i) || (false && false && false && false && f && h) ||
      (false && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00011 : ∀ f g h i j : Bool,
    circ22.eval [false, false, false, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && false && true && f && g && j) ||
      (false && false && true && true && g && i) || (false && false && false && true && f && h) ||
      (false && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00100 : ∀ f g h i j : Bool,
    circ22.eval [false, false, true, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && true && false && f && g && j) ||
      (false && false && false && false && g && i) || (false && false && true && false && f && h) ||
      (false && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00101 : ∀ f g h i j : Bool,
    circ22.eval [false, false, true, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && true && false && f && g && j) ||
      (false && false && false && true && g && i) || (false && false && true && true && f && h) ||
      (false && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00110 : ∀ f g h i j : Bool,
    circ22.eval [false, false, true, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && true && true && f && g && j) ||
      (false && false && true && false && g && i) || (false && false && true && false && f && h) ||
      (false && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk00111 : ∀ f g h i j : Bool,
    circ22.eval [false, false, true, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && true && true && f && g && j) ||
      (false && false && true && true && g && i) || (false && false && true && true && f && h) ||
      (false && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01000 : ∀ f g h i j : Bool,
    circ22.eval [false, true, false, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && false && false && f && g && j) ||
      (false && true && false && false && g && i) || (false && true && false && false && f && h) ||
      (true && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01001 : ∀ f g h i j : Bool,
    circ22.eval [false, true, false, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && false && false && f && g && j) ||
      (false && true && false && true && g && i) || (false && true && false && true && f && h) ||
      (true && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01010 : ∀ f g h i j : Bool,
    circ22.eval [false, true, false, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && false && true && f && g && j) ||
      (false && true && true && false && g && i) || (false && true && false && false && f && h) ||
      (true && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01011 : ∀ f g h i j : Bool,
    circ22.eval [false, true, false, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && false && true && f && g && j) ||
      (false && true && true && true && g && i) || (false && true && false && true && f && h) ||
      (true && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01100 : ∀ f g h i j : Bool,
    circ22.eval [false, true, true, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && true && false && f && g && j) ||
      (false && true && false && false && g && i) || (false && true && true && false && f && h) ||
      (true && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01101 : ∀ f g h i j : Bool,
    circ22.eval [false, true, true, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && true && false && f && g && j) ||
      (false && true && false && true && g && i) || (false && true && true && true && f && h) ||
      (true && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01110 : ∀ f g h i j : Bool,
    circ22.eval [false, true, true, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (false && true && true && f && g && j) ||
      (false && true && true && false && g && i) || (false && true && true && false && f && h) ||
      (true && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk01111 : ∀ f g h i j : Bool,
    circ22.eval [false, true, true, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (false && true && true && f && g && j) ||
      (false && true && true && true && g && i) || (false && true && true && true && f && h) ||
      (true && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10000 : ∀ f g h i j : Bool,
    circ22.eval [true, false, false, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && false && false && f && g && j) ||
      (true && false && false && false && g && i) || (true && false && false && false && f && h) ||
      (false && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10001 : ∀ f g h i j : Bool,
    circ22.eval [true, false, false, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && false && false && f && g && j) ||
      (true && false && false && true && g && i) || (true && false && false && true && f && h) ||
      (false && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10010 : ∀ f g h i j : Bool,
    circ22.eval [true, false, false, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && false && true && f && g && j) ||
      (true && false && true && false && g && i) || (true && false && false && false && f && h) ||
      (false && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10011 : ∀ f g h i j : Bool,
    circ22.eval [true, false, false, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && false && true && f && g && j) ||
      (true && false && true && true && g && i) || (true && false && false && true && f && h) ||
      (false && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10100 : ∀ f g h i j : Bool,
    circ22.eval [true, false, true, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && true && false && f && g && j) ||
      (true && false && false && false && g && i) || (true && false && true && false && f && h) ||
      (false && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10101 : ∀ f g h i j : Bool,
    circ22.eval [true, false, true, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && true && false && f && g && j) ||
      (true && false && false && true && g && i) || (true && false && true && true && f && h) ||
      (false && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10110 : ∀ f g h i j : Bool,
    circ22.eval [true, false, true, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && true && true && f && g && j) ||
      (true && false && true && false && g && i) || (true && false && true && false && f && h) ||
      (false && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk10111 : ∀ f g h i j : Bool,
    circ22.eval [true, false, true, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && true && true && f && g && j) ||
      (true && false && true && true && g && i) || (true && false && true && true && f && h) ||
      (false && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11000 : ∀ f g h i j : Bool,
    circ22.eval [true, true, false, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && false && false && f && g && j) ||
      (true && true && false && false && g && i) || (true && true && false && false && f && h) ||
      (true && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11001 : ∀ f g h i j : Bool,
    circ22.eval [true, true, false, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && false && false && f && g && j) ||
      (true && true && false && true && g && i) || (true && true && false && true && f && h) ||
      (true && false && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11010 : ∀ f g h i j : Bool,
    circ22.eval [true, true, false, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && false && true && f && g && j) ||
      (true && true && true && false && g && i) || (true && true && false && false && f && h) ||
      (true && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11011 : ∀ f g h i j : Bool,
    circ22.eval [true, true, false, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && false && true && f && g && j) ||
      (true && true && true && true && g && i) || (true && true && false && true && f && h) ||
      (true && false && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11100 : ∀ f g h i j : Bool,
    circ22.eval [true, true, true, false, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && true && false && f && g && j) ||
      (true && true && false && false && g && i) || (true && true && true && false && f && h) ||
      (true && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11101 : ∀ f g h i j : Bool,
    circ22.eval [true, true, true, false, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && true && false && f && g && j) ||
      (true && true && false && true && g && i) || (true && true && true && true && f && h) ||
      (true && true && false && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11110 : ∀ f g h i j : Bool,
    circ22.eval [true, true, true, true, false, f, g, h, i, j] =
    !((false && f && g && h && i && j) || (true && true && true && f && g && j) ||
      (true && true && true && false && g && i) || (true && true && true && false && f && h) ||
      (true && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem chunk11111 : ∀ f g h i j : Bool,
    circ22.eval [true, true, true, true, true, f, g, h, i, j] =
    !((true && f && g && h && i && j) || (true && true && true && f && g && j) ||
      (true && true && true && true && g && i) || (true && true && true && true && f && h) ||
      (true && true && true && h && i && j)) := by
  intro f g h i j
  cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem key22 : ∀ a b c d e f g h i j : Bool,
    circ22.eval [a, b, c, d, e, f, g, h, i, j] =
    !((e && f && g && h && i && j) || (a && c && d && f && g && j) ||
      (a && b && d && e && g && i) || (a && b && c && e && f && h) ||
      (b && c && d && h && i && j)) :=
  fun a b c d e f g h i j =>
    match a, b, c, d, e with
    | false, false, false, false, false => chunk00000 f g h i j
    | false, false, false, false, true => chunk00001 f g h i j
    | false, false, false, true, false => chunk00010 f g h i j
    | false, false, false, true, true => chunk00011 f g h i j
    | false, false, true, false, false => chunk00100 f g h i j
    | false, false, true, false, true => chunk00101 f g h i j
    | false, false, true, true, false => chunk00110 f g h i j
    | false, false, true, true, true => chunk00111 f g h i j
    | false, true, false, false, false => chunk01000 f g h i j
    | false, true, false, false, true => chunk01001 f g h i j
    | false, true, false, true, false => chunk01010 f g h i j
    | false, true, false, true, true => chunk01011 f g h i j
    | false, true, true, false, false => chunk01100 f g h i j
    | false, true, true, false, true => chunk01101 f g h i j
    | false, true, true, true, false => chunk01110 f g h i j
    | false, true, true, true, true => chunk01111 f g h i j
    | true, false, false, false, false => chunk10000 f g h i j
    | true, false, false, false, true => chunk10001 f g h i j
    | true, false, false, true, false => chunk10010 f g h i j
    | true, false, false, true, true => chunk10011 f g h i j
    | true, false, true, false, false => chunk10100 f g h i j
    | true, false, true, false, true => chunk10101 f g h i j
    | true, false, true, true, false => chunk10110 f g h i j
    | true, false, true, true, true => chunk10111 f g h i j
    | true, true, false, false, false => chunk11000 f g h i j
    | true, true, false, false, true => chunk11001 f g h i j
    | true, true, false, true, false => chunk11010 f g h i j
    | true, true, false, true, true => chunk11011 f g h i j
    | true, true, true, false, false => chunk11100 f g h i j
    | true, true, true, false, true => chunk11101 f g h i j
    | true, true, true, true, false => chunk11110 f g h i j
    | true, true, true, true, true => chunk11111 f g h i j

set_option maxHeartbeats 4000000 in
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
