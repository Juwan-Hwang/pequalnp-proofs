def adj13 (i j : Fin 13) : Bool :=
  decide ((i.val + 13 - j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))

def nbrs13 (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun j => ∃ i ∈ S, adj13 i j = true

def full13 (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun j => ∀ i : Fin 13, adj13 i j = true → i ∈ S

def pt13 (i : Fin 13) : Fin 26 := ⟨i.val, by omega⟩

def ln13 (j : Fin 13) : Fin 26 := ⟨j.val + 13, by omega⟩

lemma adj13_iff (i j : Fin 13) :
    adj13 i j = true ↔ (i.val + 13 - j.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  simp [adj13]

lemma pt13_inj : Function.Injective pt13 := by
  intro a b h
  have h2 := congrArg Fin.val h
  simp [pt13] at h2
  exact Fin.ext h2

lemma ln13_inj : Function.Injective ln13 := by
  intro a b h
  have h2 := congrArg Fin.val h
  simp [ln13] at h2
  exact Fin.ext (by omega)

lemma deg13_pt : ∀ i : Fin 13,
    (Finset.univ.filter fun j => adj13 i j = true).card = 4 := by decide

lemma deg13_ln : ∀ j : Fin 13,
    (Finset.univ.filter fun i => adj13 i j = true).card = 4 := by decide

lemma exp13_small : ∀ S : Finset (Fin 13), 2 ≤ S.card → S.card ≤ 7 →
    S.card + 5 ≤ (nbrs13 S).card := by decide

lemma exp13_big : ∀ S : Finset (Fin 13), 10 ≤ S.card → (nbrs13 S).card = 13 := by decide

lemma full13_bound : ∀ S : Finset (Fin 13), 8 ≤ S.card → S.card ≤ 12 →
    (full13 S).card ≤ S.card - 3 := by decide

lemma hGeometry : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (D : Finset (Sym2 (Fin 26))),
    (G = SimpleGraph.fromRel fun (u v : Fin 26) => u.val < 13 ∧ 13 ≤ v.val ∧
      (u.val + 26 - v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) → D.card ≤ 5 →
    (∀ K, IsMinCover (G.deleteEdges ↑D) K → K.card ≤ 12) →
    ∃ p, (Finset.univ.filter (G.Adj p)).card = 4 ∧ ∀ v, G.Adj p v → s(p,v) ∈ D := by
  intro G _ D hG hD hmin
  have hadj : ∀ u v : Fin 26, G.Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + 26 - v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + 26 - u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
    intro u v
    rw [hG, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · obtain ⟨h1, h2, h3⟩ := h
        exact ⟨fun he => by rw [he] at h1; omega, Or.inl ⟨h1, h2, h3⟩⟩
      · obtain ⟨h1, h2, h3⟩ := h
        exact ⟨fun he => by rw [he] at h2; omega, Or.inr ⟨h1, h2, h3⟩⟩
  have hadj_pt_ln : ∀ i j : Fin 13, G.Adj (pt13 i) (ln13 j) ↔ adj13 i j = true := by
    intro i j
    rw [hadj]
    have h1 : (pt13 i).val = i.val := rfl
    have h2 : (ln13 j).val = j.val + 13 := rfl
    rw [h1, h2, adj13_iff]
    have heq : i.val + 26 - (j.val + 13) = i.val + 13 - j.val := by
      have hj := j.isLt
      omega
    rw [heq]
    constructor
    · rintro (⟨-, -, h⟩ | ⟨h, -, -⟩)
      · exact h
      · exact absurd h (by omega)
    · intro h
      exact Or.inl ⟨i.isLt, by omega, h⟩
  have hdeg_pt : ∀ i : Fin 13, (Finset.univ.filter (G.Adj (pt13 i))).card = 4 := by
    intro i
    have hset : Finset.univ.filter (G.Adj (pt13 i)) =
        (Finset.univ.filter fun j => adj13 i j = true).image ln13 := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv
        rw [hadj] at hv
        rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · refine ⟨⟨v.val - 13, by have := v.isLt; omega⟩, ?_, ?_⟩
          · rw [adj13_iff]
            have heq : i.val + 13 - (v.val - 13) = i.val + 26 - v.val := by omega
            rw [heq]
            have h1' : (pt13 i).val = i.val := rfl
            rw [h1'] at h3
            exact h3
          · apply Fin.ext
            simp [ln13]
            omega
        · have h2' : (pt13 i).val = i.val := rfl
          rw [h2'] at h2
          exact absurd h2 (by have := i.isLt; omega)
      · rintro ⟨j, hj, rfl⟩
        exact (hadj_pt_ln i j).mpr hj
    rw [hset, Finset.card_image_of_injective _ ln13_inj, deg13_pt]
  have hdeg_ln : ∀ j : Fin 13, (Finset.univ.filter (G.Adj (ln13 j))).card = 4 := by
    intro j
    have hset : Finset.univ.filter (G.Adj (ln13 j)) =
        (Finset.univ.filter fun i => adj13 i j = true).image pt13 := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv
        rw [hadj] at hv
        rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have h2' : (ln13 j).val = j.val + 13 := rfl
          rw [h2'] at h1
          exact absurd h1 (by omega)
        · refine ⟨⟨v.val, by omega⟩, ?_, ?_⟩
          · rw [adj13_iff]
            have h2' : (ln13 j).val = j.val + 13 := rfl
            rw [h2'] at h3
            have heq : v.val + 13 - j.val = v.val + 26 - (j.val + 13) := by
              have hj := j.isLt
              omega
            rw [heq]
            exact h3
          · apply Fin.ext
            simp [pt13]
      · rintro ⟨i, hi, rfl⟩
        exact ((hadj_pt_ln i j).mpr hi).symm
    rw [hset, Finset.card_image_of_injective _ pt13_inj, deg13_ln]
  by_contra hcon
  push Not at hcon
  set t : Fin 13 → Finset (Fin 13) := fun i =>
    Finset.univ.filter fun j => adj13 i j = true ∧ s(pt13 i, ln13 j) ∉ D with ht
  have ht_mem : ∀ i j : Fin 13, j ∈ t i ↔ adj13 i j = true ∧ s(pt13 i, ln13 j) ∉ D := by
    intro i j
    rw [ht]
    simp
  have hHall : ∀ S : Finset (Fin 13), S.card ≤ (S.biUnion t).card := by
    intro S
    by_contra hS
    push Not at hS
    have hsub : S.biUnion t ⊆ nbrs13 S := by
      intro j hj
      rw [Finset.mem_biUnion] at hj
      obtain ⟨i, hiS, hjt⟩ := hj
      rw [ht_mem] at hjt
      simp only [nbrs13, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hiS, hjt.1⟩
    set T : Finset (Fin 13) := nbrs13 S \ S.biUnion t with hTdef
    have hTcard : T.card = (nbrs13 S).card - (S.biUnion t).card := by
      rw [hTdef]
      exact Finset.card_sdiff hsub
    have hTD : ∀ i ∈ S, ∀ j ∈ T, adj13 i j = true → s(pt13 i, ln13 j) ∈ D := by
      intro i hiS j hjT hadjij
      by_contra hnotin
      have hjbi : j ∈ S.biUnion t := by
        rw [Finset.mem_biUnion]
        exact ⟨i, hiS, (ht_mem i j).mpr ⟨hadjij, hnotin⟩⟩
      have hnotT : j ∉ T := by
        rw [hTdef, Finset.mem_sdiff]
        push Not
        intro _
        exact hjbi
      exact hnotT hjT
    set E1 : Finset (Fin 13 × Fin 13) :=
      (S ×ˢ T).filter (fun p => adj13 p.1 p.2 = true) with hE1def
    have hE1le : E1.card ≤ D.card := by
      have himg : E1.image (fun p => s(pt13 p.1, ln13 p.2)) ⊆ D := by
        intro e he
        rw [Finset.mem_image] at he
        obtain ⟨p, hp, rfl⟩ := he
        rw [hE1def, Finset.mem_filter, Finset.mem_product] at hp
        exact hTD p.1 hp.1.1 p.2 hp.1.2 hp.2
      have hinj : Set.InjOn (fun p => s(pt13 p.1, ln13 p.2)) (E1 : Set (Fin 13 × Fin 13)) := by
        intro p _ q _ hpq
        rw [Sym2.eq] at hpq
        rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext (pt13_inj h1) (ln13_inj h2)
        · have hv1 : (pt13 p.1).val = p.1.val := rfl
          have hv2 : (ln13 q.2).val = q.2.val + 13 := rfl
          have h3 := congrArg Fin.val h1
          rw [hv1, hv2] at h3
          exact absurd h3 (by have := p.1.isLt; omega)
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card himg
    have hE1ge : T.card ≤ E1.card := by
      have hMaps : Set.MapsTo Prod.snd (E1 : Set (Fin 13 × Fin 13)) (T : Set (Fin 13)) := by
        intro p hp
        rw [Finset.mem_coe, hE1def, Finset.mem_filter, Finset.mem_product] at hp
        exact Finset.mem_coe.mpr hp.1.2
      have hfiber : E1.card = ∑ j ∈ T, (E1.filter (fun p => p.2 = j)).card :=
        Finset.card_eq_sum_card_fiberwise hMaps
      rw [hfiber]
      calc T.card = ∑ _j ∈ T, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ j ∈ T, (E1.filter (fun p => p.2 = j)).card := by
            apply Finset.sum_le_sum
            intro j hjT
            have hjN : j ∈ nbrs13 S := by
              rw [hTdef, Finset.mem_sdiff] at hjT
              exact hjT.1
            simp only [nbrs13, Finset.mem_filter, Finset.mem_univ, true_and] at hjN
            obtain ⟨i, hiS, hadjij⟩ := hjN
            exact Finset.card_pos.mpr ⟨(i, j), by
              rw [Finset.mem_filter, hE1def, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨⟨hiS, hjT⟩, hadjij⟩, rfl⟩⟩
    by_cases hScard : S.card ≤ 1
    · by_cases hSc : S.card = 0
      · rw [Finset.card_eq_zero] at hSc
        rw [hSc] at hS
        simp at hS
      · have hSc1 : S.card = 1 := by omega
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hSc1
        rw [Finset.singleton_biUnion, Finset.card_singleton] at hS
        have hti : t i = ∅ := Finset.card_eq_zero.mp (by omega)
        obtain ⟨v, hvAdj, hvD⟩ := hcon (pt13 i) (hdeg_pt i)
        rw [hadj] at hvAdj
        rcases hvAdj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · set j : Fin 13 := ⟨v.val - 13, by have := v.isLt; omega⟩ with hjdef
          have hveq : v = ln13 j := by
            apply Fin.ext
            simp [ln13, hjdef]
            omega
          have hadjij : adj13 i j = true := by
            rw [adj13_iff]
            have h1' : (pt13 i).val = i.val := rfl
            rw [h1'] at h3
            have heq : i.val + 13 - j.val = i.val + 26 - v.val := by
              simp [hjdef]
              omega
            rw [heq]
            exact h3
          have hmem : s(pt13 i, ln13 j) ∈ D := by
            by_contra hnotin
            have hjt : j ∈ t i := (ht_mem i j).mpr ⟨hadjij, hnotin⟩
            rw [hti] at hjt
            exact hjt
          rw [hveq] at hvD
          exact hvD hmem
        · have h2' : (pt13 i).val = i.val := rfl
          rw [h2'] at h2
          have := i.isLt
          omega
    · by_cases hScard2 : S.card ≤ 7
      · have hexp := exp13_small S (by omega) hScard2
        omega
      · by_cases hScard3 : S.card ≤ 12
        · set E2 : Finset (Fin 13 × Fin 13) :=
            (S ×ˢ (S.biUnion t)).filter (fun p => adj13 p.1 p.2 = true) with hE2def
          have hEunion : E1 ∪ E2 =
              (S ×ˢ Finset.univ).filter (fun p => adj13 p.1 p.2 = true) := by
            ext p
            simp only [Finset.mem_union, hE1def, hE2def, Finset.mem_filter, Finset.mem_product,
              Finset.mem_univ, and_true]
            constructor
            · rintro (⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩) <;> exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              have hjN : p.2 ∈ nbrs13 S := by
                simp only [nbrs13, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨p.1, h1, h2⟩
              by_cases hj : p.2 ∈ S.biUnion t
              · exact Or.inr ⟨⟨h1, hj⟩, h2⟩
              · exact Or.inl ⟨⟨h1, by rw [hTdef, Finset.mem_sdiff]; exact ⟨hjN, hj⟩⟩, h2⟩
          have hEdisj : Disjoint E1 E2 := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            rw [hE1def, Finset.mem_filter, Finset.mem_product] at hp1
            rw [hE2def, Finset.mem_filter, Finset.mem_product] at hp2
            rw [hTdef, Finset.mem_sdiff] at hp1
            exact hp1.1.2.2 hp2.1.2
          have hEtot : E1.card + E2.card = 4 * S.card := by
            have h1 : (E1 ∪ E2).card = E1.card + E2.card :=
              Finset.card_union_of_disjoint hEdisj
            rw [hEunion] at h1
            rw [← h1]
            have hMaps : Set.MapsTo Prod.fst
                (((S ×ˢ Finset.univ).filter (fun p => adj13 p.1 p.2 = true)) :
                  Set (Fin 13 × Fin 13)) (S : Set (Fin 13)) := by
              intro p hp
              rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
              exact Finset.mem_coe.mpr hp.1.1
            have hfiber : ((S ×ˢ Finset.univ).filter (fun p => adj13 p.1 p.2 = true)).card =
                ∑ i ∈ S, (((S ×ˢ Finset.univ).filter
                  (fun p => adj13 p.1 p.2 = true)).filter (fun p => p.1 = i)).card :=
              Finset.card_eq_sum_card_fiberwise hMaps
            rw [hfiber]
            calc ∑ i ∈ S, (((S ×ˢ Finset.univ).filter
                    (fun p => adj13 p.1 p.2 = true)).filter (fun p => p.1 = i)).card
                = ∑ _i ∈ S, 4 := by
                  apply Finset.sum_congr rfl
                  intro i hiS
                  have hfiber_eq : ((S ×ˢ Finset.univ).filter
                        (fun p => adj13 p.1 p.2 = true)).filter (fun p => p.1 = i) =
                      (Finset.univ.filter fun j => adj13 i j = true).image (fun j => (i, j)) := by
                    ext p
                    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
                      Finset.mem_image]
                    constructor
                    · rintro ⟨⟨h1, h2⟩, h3⟩
                      exact ⟨p.2, by rw [← h3]; exact h2, Prod.ext h3.symm rfl⟩
                    · rintro ⟨j, hj, rfl⟩
                      exact ⟨⟨hiS, hj⟩, rfl⟩
                  rw [hfiber_eq, Finset.card_image_of_injective _
                    (fun a b h => congrArg Prod.snd h), deg13_pt]
              _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          have hE2le : E2.card ≤ 3 * (S.biUnion t).card + (full13 S).card := by
            have hMaps : Set.MapsTo Prod.snd (E2 : Set (Fin 13 × Fin 13))
                ((S.biUnion t) : Set (Fin 13)) := by
              intro p hp
              rw [Finset.mem_coe, hE2def, Finset.mem_filter, Finset.mem_product] at hp
              exact Finset.mem_coe.mpr hp.1.2
            have hfiber : E2.card = ∑ j ∈ S.biUnion t, (E2.filter (fun p => p.2 = j)).card :=
              Finset.card_eq_sum_card_fiberwise hMaps
            rw [hfiber]
            calc ∑ j ∈ S.biUnion t, (E2.filter (fun p => p.2 = j)).card
                ≤ ∑ j ∈ S.biUnion t, (3 + if j ∈ full13 S then 1 else 0) := by
                  apply Finset.sum_le_sum
                  intro j hjB
                  have hfiber_eq : (E2.filter (fun p => p.2 = j)) =
                      (S.filter fun i => adj13 i j = true).image (fun i => (i, j)) := by
                    ext p
                    simp only [hE2def, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
                    constructor
                    · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩
                      exact ⟨p.1, ⟨h1, by rw [← h3]; exact h2⟩, Prod.ext rfl h3.symm⟩
                    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
                      exact ⟨⟨⟨h1, hjB⟩, h2⟩, rfl⟩
                  rw [hfiber_eq, Finset.card_image_of_injective _
                    (fun a b h => congrArg Prod.fst h)]
                  have hsub2 : (S.filter fun i => adj13 i j = true) ⊆
                      (Finset.univ.filter fun i => adj13 i j = true) := by
                    intro x hx
                    rw [Finset.mem_filter] at hx ⊢
                    exact ⟨Finset.mem_univ x, hx.2⟩
                  by_cases hjF : j ∈ full13 S
                  · rw [if_pos hjF]
                    have hle := Finset.card_le_card hsub2
                    rw [deg13_ln] at hle
                    omega
                  · rw [if_neg hjF]
                    have hex : ∃ i₀ : Fin 13, adj13 i₀ j = true ∧ i₀ ∉ S := by
                      by_contra hc
                      push Not at hc
                      apply hjF
                      simp only [full13, Finset.mem_filter, Finset.mem_univ, true_and]
                      exact fun i hi => hc i hi
                    obtain ⟨i₀, hi₀adj, hi₀S⟩ := hex
                    have hss : (S.filter fun i => adj13 i j = true) ⊂
                        (Finset.univ.filter fun i => adj13 i j = true) := by
                      rw [Finset.ssubset_iff_subset_ne]
                      refine ⟨hsub2, ?_⟩
                      intro heq
                      have hmem : i₀ ∈ Finset.univ.filter (fun i => adj13 i j = true) := by
                        rw [Finset.mem_filter]
                        exact ⟨Finset.mem_univ i₀, hi₀adj⟩
                      rw [← heq, Finset.mem_filter] at hmem
                      exact hi₀S hmem.1
                    have hlt := Finset.card_lt_card hss
                    rw [deg13_ln] at hlt
                    omega
              _ = 3 * (S.biUnion t).card + ((S.biUnion t).filter (· ∈ full13 S)).card := by
                  rw [Finset.sum_add_distrib]
                  congr 1
                  · rw [Finset.sum_const, smul_eq_mul, mul_comm]
                  · rw [Finset.sum_boole, Nat.cast_id]
              _ ≤ 3 * (S.biUnion t).card + (full13 S).card := by
                  have hle : ((S.biUnion t).filter (· ∈ full13 S)).card ≤ (full13 S).card :=
                    Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
                  omega
          have hfull := full13_bound S (by omega) hScard3
          omega
        · have hS13 : S.card = 13 := by
            have hle : S.card ≤ 13 := by
              have h2 := Finset.card_le_univ S
              rwa [Fintype.card_fin] at h2
            omega
          have hSuniv : S = Finset.univ :=
            Finset.eq_univ_of_card S (by rw [hS13, Fintype.card_fin])
          have hN13 : (nbrs13 S).card = 13 := exp13_big S (by omega)
          have hTpos : 0 < T.card := by rw [hTcard, hN13]; omega
          obtain ⟨j, hjT⟩ := Finset.card_pos.mp hTpos
          obtain ⟨v, hvAdj, hvD⟩ := hcon (ln13 j) (hdeg_ln j)
          rw [hadj] at hvAdj
          rcases hvAdj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · have h2' : (ln13 j).val = j.val + 13 := rfl
            rw [h2'] at h1
            omega
          · set i : Fin 13 := ⟨v.val, by omega⟩ with hidef
            have hveq : v = pt13 i := by
              apply Fin.ext
              simp [pt13, hidef]
            have hadjij : adj13 i j = true := by
              rw [adj13_iff]
              have h2' : (ln13 j).val = j.val + 13 := rfl
              rw [h2'] at h3
              have heq : i.val + 13 - j.val = v.val + 26 - (j.val + 13) := by
                simp [hidef]
                have hj := j.isLt
                omega
              rw [heq]
              exact h3
            have hmem : s(pt13 i, ln13 j) ∈ D := by
              apply hTD i _ j hjT hadjij
              rw [hSuniv]
              exact Finset.mem_univ i
            rw [hveq, Sym2.eq_swap] at hvD
            exact hvD hmem
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hf_adj : ∀ i : Fin 13, G.Adj (pt13 i) (ln13 (f i)) ∧ s(pt13 i, ln13 (f i)) ∉ D := by
    intro i
    have h := hf_mem i
    rw [ht_mem] at h
    exact ⟨(hadj_pt_ln i (f i)).mpr h.1, h.2⟩
  have hex : ∃ K : Finset (Fin 26), IsMinCover (G.deleteEdges ↑D) K := by
    classical
    obtain ⟨K, hK, hKmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun T : Finset (Fin 26) =>
        (G.deleteEdges ↑D).IsVertexCover (T : Set (Fin 26)))
      Finset.card
      ⟨Finset.univ, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          rw [Finset.coe_univ]
          exact SimpleGraph.isVertexCover_univ⟩⟩
    rw [Finset.mem_filter] at hK
    refine ⟨K, ?_⟩
    show (G.deleteEdges ↑D).IsVertexCover (K : Set (Fin 26)) ∧
      ∀ T' : Finset (Fin 26), (G.deleteEdges ↑D).IsVertexCover (T' : Set (Fin 26)) →
        K.card ≤ T'.card
    exact ⟨hK.2, fun T' hT' => hKmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ T', hT'⟩)⟩
  obtain ⟨K, hK⟩ := hex
  have hKle : K.card ≤ 12 := hmin K hK
  have hKge : 13 ≤ K.card := by
    have hKcover : (G.deleteEdges ↑D).IsVertexCover (K : Set (Fin 26)) := hK.1
    have hcover : ∀ i : Fin 13, pt13 i ∈ K ∨ ln13 (f i) ∈ K := by
      intro i
      have hAdj : (G.deleteEdges ↑D).Adj (pt13 i) (ln13 (f i)) := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨(hf_adj i).1, by
          rw [Finset.mem_coe]
          exact (hf_adj i).2⟩
      have h := hKcover hAdj
      simp only [Finset.mem_coe] at h
      exact h
    set g : Fin 13 → Fin 26 := fun i => if pt13 i ∈ K then pt13 i else ln13 (f i) with hgdef
    have hgK : ∀ i : Fin 13, g i ∈ K := by
      intro i
      rw [hgdef]
      by_cases hi : pt13 i ∈ K
      · rw [if_pos hi]; exact hi
      · rw [if_neg hi]
        rcases hcover i with h | h
        · exact absurd h hi
        · exact h
    have hg_inj : Function.Injective g := by
      intro a b hab
      rw [hgdef] at hab
      by_cases ha : pt13 a ∈ K <;> by_cases hb : pt13 b ∈ K <;>
        simp only [ha, hb, ↓reduceIte] at hab
      · exact pt13_inj hab
      · have hv1 : (pt13 a).val = a.val := rfl
        have hv2 : (ln13 (f b)).val = (f b).val + 13 := rfl
        have h3 := congrArg Fin.val hab
        rw [hv1, hv2] at h3
        exact absurd h3 (by have := a.isLt; omega)
      · have hv1 : (ln13 (f a)).val = (f a).val + 13 := rfl
        have hv2 : (pt13 b).val = b.val := rfl
        have h3 := congrArg Fin.val hab
        rw [hv1, hv2] at h3
        exact absurd h3 (by have := b.isLt; omega)
      · exact hf_inj (ln13_inj hab)
    have hcard : (Finset.univ.image g).card ≤ K.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hgK i
    rw [Finset.card_image_of_injective _ hg_inj] at hcard
    simpa using hcard
  omega
