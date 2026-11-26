import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3786_aux

open PEqualNP.CircuitLowerBounds

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true


/-- Values of the 21 vertices. Positions 0..8 form the left side with values
    2,4,5,6,7,8,10,11,12 (the complement of {0,1,3,9} modulo 13); positions
    9..20 form the right side with values 1..12. -/
def val21 (p : Fin 21) : ℕ :=
  match p.val with
  | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 8 | 6 => 10 | 7 => 11 | 8 => 12
  | n => n - 8

def adj21 (p q : Fin 21) : Prop :=
  (p.val < 9 ∧ 9 ≤ q.val ∧ (val21 p + val21 q) % 13 ∈ [0, 1, 3, 9]) ∨
  (q.val < 9 ∧ 9 ≤ p.val ∧ (val21 q + val21 p) % 13 ∈ [0, 1, 3, 9])

instance : DecidableRel adj21 := fun p q => by unfold adj21; infer_instance

def H21 : SimpleGraph (Fin 21) where
  Adj := adj21
  symm := by
    constructor
    intro v w h
    unfold adj21 at h ⊢
    tauto
  loopless := by
    constructor
    intro v h
    unfold adj21 at h
    rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> omega

instance : DecidableRel H21.Adj := fun p q => by
  show Decidable (adj21 p q)
  infer_instance

lemma H21_adj {p q : Fin 21} : H21.Adj p q ↔ adj21 p q := Iff.rfl

lemma val21_lt13 (p : Fin 21) : val21 p < 13 := by
  fin_cases p <;> decide

lemma val21_not_mem {p : Fin 21} (h : p.val < 9) : val21 p ∉ [0, 1, 3, 9] := by
  have hall : ∀ p : Fin 21, p.val < 9 → val21 p ∉ [0, 1, 3, 9] := by decide
  exact hall p h

lemma val21_ge {p : Fin 21} (h : 9 ≤ p.val) : val21 p = p.val - 8 := by
  have hall : ∀ p : Fin 21, 9 ≤ p.val → val21 p = p.val - 8 := by decide
  exact hall p h

lemma val21_inj_lt {p q : Fin 21} (hp : p.val < 9) (hq : q.val < 9)
    (h : val21 p = val21 q) : p = q := by
  have hall : ∀ a b : Fin 21, a.val < 9 → b.val < 9 → val21 a = val21 b → a.val = b.val := by
    decide
  exact Fin.ext (hall p q hp hq h)

lemma val21_inj_ge {p q : Fin 21} (hp : 9 ≤ p.val) (hq : 9 ≤ q.val)
    (h : val21 p = val21 q) : p = q := by
  rw [val21_ge hp, val21_ge hq] at h
  apply Fin.ext
  omega

lemma adj21_iff {p q : Fin 21} : adj21 p q ↔
    ((p.val < 9 ∧ 9 ≤ q.val) ∨ (q.val < 9 ∧ 9 ≤ p.val)) ∧
    (val21 p + val21 q) % 13 ∈ [0, 1, 3, 9] := by
  unfold adj21
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨Or.inl ⟨h1, h2⟩, h3⟩
    · refine ⟨Or.inr ⟨h1, h2⟩, ?_⟩
      rw [Nat.add_comm (val21 p) (val21 q)]
      exact h3
  · rintro ⟨(⟨h1, h2⟩ | ⟨h1, h2⟩), h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · refine Or.inr ⟨h1, h2, ?_⟩
      rw [Nat.add_comm (val21 q) (val21 p)]
      exact h3

lemma diff_unique : ∀ d1 ∈ ([0, 1, 3, 9] : List ℕ), ∀ d2 ∈ ([0, 1, 3, 9] : List ℕ),
    ∀ d3 ∈ ([0, 1, 3, 9] : List ℕ), ∀ d4 ∈ ([0, 1, 3, 9] : List ℕ),
    d1 ≠ d2 → (d1 + 13 - d2) % 13 = (d3 + 13 - d4) % 13 → d1 = d3 ∧ d2 = d4 := by decide

lemma H21_c4free : ∀ a b c d : Fin 21, a ≠ c → b ≠ d →
    ¬ (H21.Adj a b ∧ H21.Adj b c ∧ H21.Adj c d ∧ H21.Adj d a) := by
  intro a b c d hac hbd h
  obtain ⟨hab, hbc, hcd, hda⟩ := h
  rw [H21_adj, adj21_iff] at hab hbc hcd hda
  obtain ⟨habS, habV⟩ := hab
  obtain ⟨hbcS, hbcV⟩ := hbc
  obtain ⟨hcdS, hcdV⟩ := hcd
  obtain ⟨hdaS, hdaV⟩ := hda
  have ha13 := val21_lt13 a
  have hb13 := val21_lt13 b
  have hc13 := val21_lt13 c
  have hd13 := val21_lt13 d
  have hside : (a.val < 9 ∧ c.val < 9 ∧ 9 ≤ b.val ∧ 9 ≤ d.val) ∨
      (9 ≤ a.val ∧ 9 ≤ c.val ∧ b.val < 9 ∧ d.val < 9) := by
    rcases habS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hbcS with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hcdS with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      rcases hdaS with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;> omega
  rcases hside with ⟨ha9, hc9, hb9, hd9⟩ | ⟨ha9, hc9, hb9, hd9⟩
  · have hbcV' : (val21 c + val21 b) % 13 ∈ [0, 1, 3, 9] := by
      rwa [Nat.add_comm] at hbcV
    have hdaV' : (val21 a + val21 d) % 13 ∈ [0, 1, 3, 9] := by
      rwa [Nat.add_comm] at hdaV
    have hmodeq : ((val21 a + val21 b) % 13 + 13 - (val21 c + val21 b) % 13) % 13 =
        ((val21 a + val21 d) % 13 + 13 - (val21 c + val21 d) % 13) % 13 := by omega
    have hvac : val21 a ≠ val21 c := fun h => hac (val21_inj_lt ha9 hc9 h)
    have hne : (val21 a + val21 b) % 13 ≠ (val21 c + val21 b) % 13 := by omega
    have hdiff := diff_unique _ habV _ hbcV' _ hdaV' _ hcdV hne hmodeq
    have hvb : val21 b = val21 d := by omega
    exact hbd (val21_inj_ge hb9 hd9 hvb)
  · have habV' : (val21 b + val21 a) % 13 ∈ [0, 1, 3, 9] := by
      rwa [Nat.add_comm] at habV
    have hcdV' : (val21 d + val21 c) % 13 ∈ [0, 1, 3, 9] := by
      rwa [Nat.add_comm] at hcdV
    have hmodeq : ((val21 b + val21 a) % 13 + 13 - (val21 b + val21 c) % 13) % 13 =
        ((val21 d + val21 a) % 13 + 13 - (val21 d + val21 c) % 13) % 13 := by omega
    have hvac : val21 a ≠ val21 c := fun h => hac (val21_inj_ge ha9 hc9 h)
    have hne : (val21 b + val21 a) % 13 ≠ (val21 b + val21 c) % 13 := by omega
    have hdiff := diff_unique _ habV' _ hbcV _ hdaV _ hcdV' hne hmodeq
    have hvb : val21 b = val21 d := by omega
    exact hbd (val21_inj_lt hb9 hd9 hvb)

lemma H21_degree_lt {p : Fin 21} (h : p.val < 9) : H21.degree p = 4 := by
  have ha13 : val21 p < 13 := val21_lt13 p
  have haD : val21 p ∉ [0, 1, 3, 9] := val21_not_mem h
  have hcard : (H21.neighborFinset p).card = ({0, 1, 3, 9} : Finset ℕ).card := by
    apply Finset.card_bij (fun q _ => (val21 p + val21 q) % 13)
    · intro q hq
      rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff] at hq
      simpa using hq.2
    · intro q1 hq1 q2 hq2 heq
      rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff] at hq1 hq2
      have hq1ge : 9 ≤ q1.val := by rcases hq1.1 with ⟨-, h2⟩ | ⟨h1, -⟩ <;> omega
      have hq2ge : 9 ≤ q2.val := by rcases hq2.1 with ⟨-, h2⟩ | ⟨h1, -⟩ <;> omega
      have hv1 : val21 q1 < 13 := val21_lt13 q1
      have hv2 : val21 q2 < 13 := val21_lt13 q2
      have h1ge : 1 ≤ val21 q1 := by rw [val21_ge hq1ge]; omega
      have h2ge : 1 ≤ val21 q2 := by rw [val21_ge hq2ge]; omega
      have hveq : val21 q1 = val21 q2 := by omega
      exact val21_inj_ge hq1ge hq2ge hveq
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      have hd13 : d < 13 := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
      have hda : d ≠ val21 p := by
        intro hcon
        apply haD
        rw [← hcon]
        rcases hd with rfl | rfl | rfl | rfl <;> simp
      have hqval : val21 ⟨(d + 13 - val21 p) % 13 + 8, by omega⟩ =
          (d + 13 - val21 p) % 13 := by
        rw [val21_ge (by show 9 ≤ (d + 13 - val21 p) % 13 + 8; omega)]
        simp
      refine ⟨⟨(d + 13 - val21 p) % 13 + 8, by omega⟩, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff]
        refine ⟨Or.inl ⟨h, by show 9 ≤ (d + 13 - val21 p) % 13 + 8; omega⟩, ?_⟩
        rw [hqval]
        have hsum : (val21 p + (d + 13 - val21 p) % 13) % 13 = d := by omega
        rw [hsum]
        rcases hd with rfl | rfl | rfl | rfl <;> simp
      · show (val21 p + val21 ⟨(d + 13 - val21 p) % 13 + 8, by omega⟩) % 13 = d
        rw [hqval]
        omega
  have hdeg : H21.degree p = (H21.neighborFinset p).card := rfl
  rw [hdeg, hcard]
  decide

lemma Rdeg_aux : ∀ b : Fin 13, b.val ≠ 0 →
    (({0, 1, 3, 9} : Finset ℕ).filter
      (fun d => (d + 13 - b.val) % 13 ∉ [0, 1, 3, 9])).card = 3 := by
  decide

lemma H21_degree_ge {q : Fin 21} (h : 9 ≤ q.val) : H21.degree q = 3 := by
  have hb13 : val21 q < 13 := val21_lt13 q
  have hb1 : 1 ≤ val21 q := by rw [val21_ge h]; omega
  have hcard : (H21.neighborFinset q).card =
      (({0, 1, 3, 9} : Finset ℕ).filter
        (fun d => (d + 13 - val21 q) % 13 ∉ [0, 1, 3, 9])).card := by
    apply Finset.card_bij (fun p _ => (val21 p + val21 q) % 13)
    · intro p hp
      rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff] at hp
      have hp9 : p.val < 9 := by rcases hp.1 with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨by rw [Nat.add_comm (val21 p) (val21 q)]; simpa using hp.2, ?_⟩
      have hback : ((val21 p + val21 q) % 13 + 13 - val21 q) % 13 = val21 p := by
        have := val21_lt13 p
        omega
      rw [hback]
      exact val21_not_mem hp9
    · intro p1 hp1 p2 hp2 heq
      rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff] at hp1 hp2
      have hp19 : p1.val < 9 := by rcases hp1.1 with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
      have hp29 : p2.val < 9 := by rcases hp2.1 with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
      have hv1 : val21 p1 < 13 := val21_lt13 p1
      have hv2 : val21 p2 < 13 := val21_lt13 p2
      have hveq : val21 p1 = val21 p2 := by omega
      exact val21_inj_lt hp19 hp29 hveq
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hd
      obtain ⟨hdD, hdnot⟩ := hd
      have hd13 : d < 13 := by rcases hdD with rfl | rfl | rfl | rfl <;> norm_num
      set v := (d + 13 - val21 q) % 13 with hv
      have hv13 : v < 13 := Nat.mod_lt _ (by norm_num)
      have hvL : v ∈ [2, 4, 5, 6, 7, 8, 10, 11, 12] := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hdnot ⊢
        omega
      have hex : ∃ p : Fin 21, p.val < 9 ∧ val21 p = v := by
        interval_cases v
        · simp at hvL
        · simp at hvL
        · exact ⟨0, by norm_num, by decide⟩
        · simp at hvL
        · exact ⟨1, by norm_num, by decide⟩
        · exact ⟨2, by norm_num, by decide⟩
        · exact ⟨3, by norm_num, by decide⟩
        · exact ⟨4, by norm_num, by decide⟩
        · exact ⟨5, by norm_num, by decide⟩
        · simp at hvL
        · exact ⟨6, by norm_num, by decide⟩
        · exact ⟨7, by norm_num, by decide⟩
        · exact ⟨8, by norm_num, by decide⟩
      obtain ⟨p, hp9, hpv⟩ := hex
      refine ⟨p, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset, H21_adj, adj21_iff]
        refine ⟨Or.inr ⟨hp9, h⟩, ?_⟩
        rw [hpv]
        have hsum : (val21 q + v) % 13 = d := by omega
        rw [hsum]
        rcases hdD with rfl | rfl | rfl | rfl <;> simp
      · rw [hpv]
        omega
  have hdeg : H21.degree q = (H21.neighborFinset q).card := rfl
  have hfin : (({0, 1, 3, 9} : Finset ℕ).filter
        (fun d => (d + 13 - val21 q) % 13 ∉ [0, 1, 3, 9])).card = 3 := by
    have := Rdeg_aux ⟨val21 q, hb13⟩ (by show val21 q ≠ 0; omega)
    simpa using this
  rw [hdeg, hcard, hfin]

lemma H21_edges : H21.edgeFinset.card = 36 := by
  have hsum : ∑ v : Fin 21, H21.degree v =
      ∑ v : Fin 21, (if v.val < 9 then 4 else 3) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v.val < 9
    · rw [if_pos hv]; exact H21_degree_lt hv
    · rw [if_neg hv]; exact H21_degree_ge (by omega)
  have h72 : ∑ v : Fin 21, (if v.val < 9 then (4 : ℕ) else 3) = 72 := by decide
  have htot := SimpleGraph.sum_degrees_eq_twice_card_edges (G := H21)
  omega

/-- The matching partner of a left vertex, as a raw natural number. -/
def matchNum (i : ℕ) : ℕ :=
  match i with
  | 0 => 9 | 1 => 13 | 2 => 12 | 3 => 11 | 4 => 10 | 5 => 14 | 6 => 20 | 7 => 19 | 8 => 18
  | _ => 0

lemma H21_cover_card {T : Finset (Fin 21)}
    (hT : ∀ u v, H21.Adj u v → u ∈ T ∨ v ∈ T) : 9 ≤ T.card := by
  have hmatch : ∀ p : Fin 21, p.val < 9 →
      9 ≤ (⟨matchNum p.val % 21, Nat.mod_lt _ (by norm_num)⟩ : Fin 21).val ∧
      H21.Adj p ⟨matchNum p.val % 21, Nat.mod_lt _ (by norm_num)⟩ := by
    intro p hp
    fin_cases p <;> first | decide | (simp at hp)
  have hmatch_inj : ∀ p q : Fin 21, p.val < 9 → q.val < 9 →
      (⟨matchNum p.val % 21, Nat.mod_lt _ (by norm_num)⟩ : Fin 21) =
      ⟨matchNum q.val % 21, Nat.mod_lt _ (by norm_num)⟩ → p = q := by
    intro p q hp hq heq
    have hlt : ∀ i : ℕ, i < 9 → matchNum i < 21 := by
      intro i hi
      interval_cases i <;> decide
    have hinj : ∀ a b : Fin 21, a.val < 9 → b.val < 9 →
        matchNum a.val = matchNum b.val → a.val = b.val := by decide
    have hval : matchNum p.val % 21 = matchNum q.val % 21 := by
      have := congrArg Fin.val heq
      simpa using this
    have hmn : matchNum p.val = matchNum q.val := by
      have h1 := hlt p.val hp
      have h2 := hlt q.val hq
      omega
    exact Fin.ext (hinj p q hp hq hmn)
  have hle : (Finset.univ.filter (fun p : Fin 21 => p.val < 9)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun p => if p ∈ T then p else ⟨matchNum p.val % 21, Nat.mod_lt _ (by norm_num)⟩)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      by_cases hpT : p ∈ T
      · simp only [if_pos hpT]; exact hpT
      · simp only [if_neg hpT]
        rcases hT p _ (hmatch p hp).2 with h | h
        · exact absurd h hpT
        · exact h
    · intro p hp q hq heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      by_cases hpT : p ∈ T <;> by_cases hqT : q ∈ T
      · simp only [hpT, hqT, ite_true, ite_false] at heq
        exact heq
      · simp only [hpT, hqT, ite_true, ite_false] at heq
        have hge := (hmatch q hq).1
        rw [← heq] at hge
        omega
      · simp only [hpT, hqT, ite_true, ite_false] at heq
        have hge := (hmatch p hp).1
        rw [heq] at hge
        omega
      · simp only [hpT, hqT, ite_true, ite_false] at heq
        exact hmatch_inj p q hp hq heq
  have hs9 : (Finset.univ.filter (fun p : Fin 21 => p.val < 9)).card = 9 := by decide
  omega

/-- The list of 26-values from the statement. -/
def L26 : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

/-- The input function from the statement. -/
def x3fun (A B : Finset (Fin 13)) (v : Fin 26) : Bool :=
  if v.val < 13 then decide (Fin.ofNat 13 v.val ∈ A)
  else decide (Fin.ofNat 13 v.val ∈ B)

lemma ofNat13_of_lt {k : ℕ} (h : k < 13) : Fin.ofNat 13 k = ⟨k, h⟩ := by
  apply Fin.ext
  simp only [Fin.ofNat, Fin.val_mk]
  exact Nat.mod_eq_of_lt h

lemma ofNat13_of_ge {k : ℕ} (h1 : 13 ≤ k) (h2 : k < 26) :
    Fin.ofNat 13 k = ⟨k - 13, by omega⟩ := by
  apply Fin.ext
  simp only [Fin.ofNat, Fin.val_mk]
  omega

lemma x3fun_lt {A B : Finset (Fin 13)} {v : Fin 26} (h : v.val < 13) :
    x3fun A B v = decide (⟨v.val, h⟩ ∈ A) := by
  unfold x3fun
  rw [if_pos h, ofNat13_of_lt h]

lemma x3fun_ge {A B : Finset (Fin 13)} {v : Fin 26} (h1 : 13 ≤ v.val) (h2 : v.val < 26) :
    x3fun A B v = decide (⟨v.val - 13, by omega⟩ ∈ B) := by
  unfold x3fun
  rw [if_neg (by omega), ofNat13_of_ge h1 h2]

lemma eval_iff_edgeTrue {C : Circuit}
    (heval : ∀ A B : Finset (Fin 13), C.eval (List.map (x3fun A B) L26) = true ↔
      ∃ a ∈ A, a.val ∉ [0, 1, 3, 9] ∧ ∃ b ∈ B, (a.val + b.val) % 13 ∈ [0, 1, 3, 9])
    (x : Fin 21 → Bool) :
    C.eval (List.ofFn x) = true ↔ edgeTrue H21 x := by
  let A : Finset (Fin 13) :=
    (Finset.univ.filter (fun p : Fin 21 => p.val < 9 ∧ x p = true)).image
      (fun p => ⟨val21 p % 13, Nat.mod_lt _ (by norm_num)⟩)
  let B : Finset (Fin 13) :=
    (Finset.univ.filter (fun p : Fin 21 => 9 ≤ p.val ∧ x p = true)).image
      (fun p => ⟨val21 p % 13, Nat.mod_lt _ (by norm_num)⟩)
  have hA : ∀ p : Fin 21, p.val < 9 →
      ((⟨val21 p % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) ∈ A ↔ x p = true) := by
    intro p hp
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, ⟨hq9, hqx⟩, hqeq⟩
      have hveq : val21 q = val21 p := by
        have h1 : val21 q < 13 := val21_lt13 q
        have h2 : val21 p < 13 := val21_lt13 p
        have h3 : val21 q % 13 = val21 p % 13 := by
          have := congrArg Fin.val hqeq
          simpa using this
        omega
      have hqp : q = p := val21_inj_lt hq9 hp hveq
      rwa [hqp] at hqx
    · intro hx
      exact ⟨p, ⟨hp, hx⟩, rfl⟩
  have hB : ∀ p : Fin 21, 9 ≤ p.val →
      ((⟨val21 p % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) ∈ B ↔ x p = true) := by
    intro p hp
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, ⟨hq9, hqx⟩, hqeq⟩
      have hveq : val21 q = val21 p := by
        have h1 : val21 q < 13 := val21_lt13 q
        have h2 : val21 p < 13 := val21_lt13 p
        have h3 : val21 q % 13 = val21 p % 13 := by
          have := congrArg Fin.val hqeq
          simpa using this
        omega
      have hqp : q = p := val21_inj_ge hq9 hp hveq
      rwa [hqp] at hqx
    · intro hx
      exact ⟨p, ⟨hp, hx⟩, rfl⟩
  have hlist : List.map (x3fun A B) L26 = List.ofFn x := by
    apply List.ext_getElem
    · simp [L26]
    · intro i hi1 hi2
      have hi21 : i < 21 := by simpa [L26] using hi1
      have hi0 : 0 ≤ i := Nat.zero_le i
      rw [List.getElem_map, List.getElem_ofFn]
      by_cases hi9 : i < 9
      · have hL : (L26[i]'hi1).val = val21 ⟨i, hi21⟩ := by
          interval_cases i <;> rfl
        have hlt : (L26[i]'hi1).val < 13 := by rw [hL]; exact val21_lt13 _
        show x3fun A B (L26[i]'hi1) = x ⟨i, hi21⟩
        rw [x3fun_lt hlt]
        have hfin : (⟨(L26[i]'hi1).val, hlt⟩ : Fin 13) =
            ⟨val21 ⟨i, hi21⟩ % 13, Nat.mod_lt _ (by norm_num)⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          rw [hL, Nat.mod_eq_of_lt (val21_lt13 _)]
        rw [hfin]
        by_cases hx : x ⟨i, hi21⟩ = true
        · rw [hx]
          simp only [decide_eq_true_eq]
          exact (hA ⟨i, hi21⟩ hi9).mpr hx
        · have hxf : x ⟨i, hi21⟩ = false := by
            cases h : x ⟨i, hi21⟩ <;> simp_all
          rw [hxf]
          simp only [decide_eq_false_iff_not]
          exact fun hmem => hx ((hA ⟨i, hi21⟩ hi9).mp hmem)
      · have hi9' : 9 ≤ i := by omega
        have hL : (L26[i]'hi1).val = i + 5 := by
          interval_cases i <;> rfl
        have h1 : 13 ≤ (L26[i]'hi1).val := by rw [hL]; omega
        have h2 : (L26[i]'hi1).val < 26 := by rw [hL]; omega
        show x3fun A B (L26[i]'hi1) = x ⟨i, hi21⟩
        rw [x3fun_ge h1 h2]
        have hfin : (⟨(L26[i]'hi1).val - 13, by omega⟩ : Fin 13) =
            ⟨val21 ⟨i, hi21⟩ % 13, Nat.mod_lt _ (by norm_num)⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          rw [hL, show val21 ⟨i, hi21⟩ = i - 8 from val21_ge hi9']
          omega
        rw [hfin]
        by_cases hx : x ⟨i, hi21⟩ = true
        · rw [hx]
          simp only [decide_eq_true_eq]
          exact (hB ⟨i, hi21⟩ hi9').mpr hx
        · have hxf : x ⟨i, hi21⟩ = false := by
            cases h : x ⟨i, hi21⟩ <;> simp_all
          rw [hxf]
          simp only [decide_eq_false_iff_not]
          exact fun hmem => hx ((hB ⟨i, hi21⟩ hi9').mp hmem)
  rw [← hlist, heval A B]
  constructor
  · rintro ⟨a, haA, haD, b, hbB, hab⟩
    obtain ⟨p, ⟨hp9, hpx⟩, hpa⟩ :
        ∃ p, (p.val < 9 ∧ x p = true) ∧
          (⟨val21 p % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = a := by
      simpa [A] using haA
    obtain ⟨q, ⟨hq9, hqx⟩, hqb⟩ :
        ∃ q, (9 ≤ q.val ∧ x q = true) ∧
          (⟨val21 q % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = b := by
      simpa [B] using hbB
    have hpa' : val21 p = a.val := by
      have h3 := congrArg Fin.val hpa
      simp only [Fin.val_mk] at h3
      rwa [Nat.mod_eq_of_lt (val21_lt13 p)] at h3
    have hqb' : val21 q = b.val := by
      have h3 := congrArg Fin.val hqb
      simp only [Fin.val_mk] at h3
      rwa [Nat.mod_eq_of_lt (val21_lt13 q)] at h3
    refine ⟨p, q, ?_, hpx, hqx⟩
    rw [H21_adj, adj21_iff]
    exact ⟨Or.inl ⟨hp9, hq9⟩, by rw [hpa', hqb']; exact hab⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    rw [H21_adj, adj21_iff] at huv
    obtain ⟨hsides, hsum⟩ := huv
    rcases hsides with ⟨hu9, hv9⟩ | ⟨hv9, hu9⟩
    · refine ⟨⟨val21 u % 13, Nat.mod_lt _ (by norm_num)⟩, (hA u hu9).mpr hu, ?_,
        ⟨val21 v % 13, Nat.mod_lt _ (by norm_num)⟩, (hB v hv9).mpr hv, ?_⟩
      · simp only [Fin.val_mk, Nat.mod_eq_of_lt (val21_lt13 u)]
        exact val21_not_mem hu9
      · simp only [Fin.val_mk, Nat.mod_eq_of_lt (val21_lt13 u),
          Nat.mod_eq_of_lt (val21_lt13 v)]
        exact hsum
    · refine ⟨⟨val21 v % 13, Nat.mod_lt _ (by norm_num)⟩, (hA v hv9).mpr hv, ?_,
        ⟨val21 u % 13, Nat.mod_lt _ (by norm_num)⟩, (hB u hu9).mpr hu, ?_⟩
      · simp only [Fin.val_mk, Nat.mod_eq_of_lt (val21_lt13 v)]
        exact val21_not_mem hv9
      · simp only [Fin.val_mk, Nat.mod_eq_of_lt (val21_lt13 v),
          Nat.mod_eq_of_lt (val21_lt13 u)]
        rwa [Nat.add_comm] at hsum

end PEqualNP.Outside.L_meta_3786_aux
