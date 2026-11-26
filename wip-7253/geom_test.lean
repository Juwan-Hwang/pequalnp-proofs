import Mathlib

def adj13 (i j : Fin 13) : Prop := (i.val + 13 - j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

instance : DecidableRel adj13 := fun i j => by unfold adj13; infer_instance

def nbrs (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun j => ∃ i ∈ S, adj13 i j

def fullLines (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun j => ∀ i : Fin 13, adj13 i j → i ∈ S

example : ∀ i : Fin 13, (Finset.univ.filter fun j => adj13 i j).card = 4 := by decide
example : ∀ j : Fin 13, (Finset.univ.filter fun i => adj13 i j).card = 4 := by decide
