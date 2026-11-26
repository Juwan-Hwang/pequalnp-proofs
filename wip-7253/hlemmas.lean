lemma hNoAlias : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    IsLeastAO G C → ∀ a w : ℕ, a < C.gates.length → w < n + a →
    (∀ x : Fin n → Bool, gateVal n C a x = wireVal n C w x) → False := by
  intro n G _ C hL a w ha hw hEq
  obtain ⟨hAO2, hfun, hmin⟩ := hL
  have hAO : M1528.P1.S98.AO n C := M1528.P1.S98.AO_of_IsAO2 n C hAO2
  have hLeast : M1528.P1.S98.Least n C := by
    refine ⟨hAO, ?_⟩
    intro D hD hDfun
    have hD2 : PEqualNP.TopForm.IsAO2 n D := M1528.P1.S98.IsAO2_of_AO n D hD
    have hDfun2 : circuitFun n D = graphFun G ∅ := by
      funext x
      have h1 : circuitFun n D x = D.eval (List.ofFn x) := rfl
      have h2 : circuitFun n C x = C.eval (List.ofFn x) := rfl
      rw [h1, hDfun x, ← h2]
      exact congrFun hfun x
    have hsize := hmin D hD2 hDfun2
    exact hsize
  obtain ⟨x, hx⟩ := M1528.P1.S98.least_nodup n C hLeast w a hw ha
  apply hx
  have h := hEq x
  exact h.symm

lemma hTrace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    IsLeastAO G C → TopForm G C → ∀ p v : Fin n, s(p,v) ∈ Ustar G C →
    ∃ a ∈ junk G C, ∀ b : Fin 2, p ∈ side (n := n) C a b ∨ v ∈ side (n := n) C a b := by
  intro n G _ C hL _hT p v hpv
  obtain ⟨hAO2, hfun, _hmin⟩ := hL
  have hAO : M1528.P1.S98.AO n C := M1528.P1.S98.AO_of_IsAO2 n C hAO2
  have hmem := Finset.mem_sdiff.mp hpv
  have hEdge : G.Adj p v :=
    SimpleGraph.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hmem.1)
  have hNotStar : s(p,v) ∉ starEdges G C := hmem.2
  have claim : ∀ w : ℕ, w < n + C.gates.length →
      M1528.P1.S98.W n C (pairInput p v) w = true →
      (M1528.P2.OrR n C w p.val ∨ M1528.P2.OrR n C w v.val) ∨
      ∃ a ∈ junk G C, ∀ b : Fin 2, p ∈ side (n := n) C a b ∨ v ∈ side (n := n) C a b := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hW
      by_cases hwlt : w < n
      · left
        rw [M1528.P1.S98.W_input n C _ w hwlt] at hW
        rw [M1528.P2.pairInput_true] at hW
        rcases hW with h | h
        · left
          have h2 : w = p.val := congrArg Fin.val h
          rw [h2]
          exact Relation.ReflTransGen.refl
        · right
          have h2 : w = v.val := congrArg Fin.val h
          rw [h2]
          exact Relation.ReflTransGen.refl
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨hop, a0, b0, hab, ha0, hb0⟩ := hAO k hk
        have hin := M1528.P2.opnd_eq n C hAO k hk
        have hlt := M1528.P2.opnd_lt n C hAO k hk (opnd C k) hin
        rcases hop with hop | hop
        · -- AND gate
          rw [M1528.P1.S98.W_and n C _ k hk hop (opnd C k 0) (opnd C k 1) hin (hlt 0) (hlt 1)] at hW
          have h0 : M1528.P1.S98.W n C (pairInput p v) (opnd C k 0) = true :=
            ((Bool.and_eq_true _ _).mp hW).1
          have h1 : M1528.P1.S98.W n C (pairInput p v) (opnd C k 1) = true :=
            ((Bool.and_eq_true _ _).mp hW).2
          have ih0 := ih (opnd C k 0) (hlt 0) (by omega) h0
          have ih1 := ih (opnd C k 1) (hlt 1) (by omega) h1
          rcases ih0 with h0r | h0j
          · rcases ih1 with h1r | h1j
            · -- both OrR: side memberships
              have hs0 : p ∈ side (n := n) C k 0 ∨ v ∈ side (n := n) C k 0 := by
                rcases h0r with h | h
                · exact Or.inl ((M1528.P2.mem_orIn n C hAO (opnd C k 0) (by omega) p).mpr h)
                · exact Or.inr ((M1528.P2.mem_orIn n C hAO (opnd C k 0) (by omega) v).mpr h)
              have hs1 : p ∈ side (n := n) C k 1 ∨ v ∈ side (n := n) C k 1 := by
                rcases h1r with h | h
                · exact Or.inl ((M1528.P2.mem_orIn n C hAO (opnd C k 1) (by omega) p).mpr h)
                · exact Or.inr ((M1528.P2.mem_orIn n C hAO (opnd C k 1) (by omega) v).mpr h)
              by_cases hbel : BelowF G C k
              · -- top: contradictions
                have hktop : k ∈ tops G C :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hbel⟩
                rcases hs0 with hp0 | hv0 <;> rcases hs1 with hp1 | hv1
                · -- p in both sides: gate true at pairInput p p
                  have hpp : M1528.P1.S98.W n C (pairInput p p) p.val = true := by
                    rw [M1528.P1.S98.W_input n C _ p.val p.isLt]
                    exact (M1528.P2.pairInput_true p p ⟨p.val, p.isLt⟩).mpr (Or.inl rfl)
                  have hg : M1528.P1.S98.W n C (pairInput p p) (n + k) = true := by
                    apply M1528.P2.top_true n C hAO k hk hop (opnd C k) hin
                    intro b
                    rcases M1528.P2.fin2_sub b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb]
                    · exact M1528.P2.orR_mono n C hAO _ _ _ ((M1528.P2.mem_orIn n C hAO (opnd C k 0) (by omega) p).mp hp0) hpp
                    · exact M1528.P2.orR_mono n C hAO _ _ _ ((M1528.P2.mem_orIn n C hAO (opnd C k 1) (by omega) p).mp hp1) hpp
                  have hF : graphFun G ∅ (pairInput p p) = true := hbel (pairInput p p) hg
                  exact (G.irrefl ((M1528.P2.graphFun_pair G p p).mp hF)).elim
                · -- p in side 0, v in side 1: star edge
                  have hstar : s(p,v) ∈ starEdges G C := by
                    rw [Finset.mem_biUnion]
                    exact ⟨k, hktop, Finset.mem_image.mpr ⟨(p, v), Finset.mem_product.mpr ⟨hp0, hv1⟩, rfl⟩⟩
                  exact (hNotStar hstar).elim
                · -- v in side 0, p in side 1: star edge (swap)
                  have hstar : s(v,p) ∈ starEdges G C := by
                    rw [Finset.mem_biUnion]
                    exact ⟨k, hktop, Finset.mem_image.mpr ⟨(v, p), Finset.mem_product.mpr ⟨hv0, hp1⟩, rfl⟩⟩
                  rw [Sym2.eq_swap] at hstar
                  exact (hNotStar hstar).elim
                · -- v in both sides: gate true at pairInput v v
                  have hvv : M1528.P1.S98.W n C (pairInput v v) v.val = true := by
                    rw [M1528.P1.S98.W_input n C _ v.val v.isLt]
                    exact (M1528.P2.pairInput_true v v ⟨v.val, v.isLt⟩).mpr (Or.inl rfl)
                  have hg : M1528.P1.S98.W n C (pairInput v v) (n + k) = true := by
                    apply M1528.P2.top_true n C hAO k hk hop (opnd C k) hin
                    intro b
                    rcases M1528.P2.fin2_sub b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb]
                    · exact M1528.P2.orR_mono n C hAO _ _ _ ((M1528.P2.mem_orIn n C hAO (opnd C k 0) (by omega) v).mp hv0) hvv
                    · exact M1528.P2.orR_mono n C hAO _ _ _ ((M1528.P2.mem_orIn n C hAO (opnd C k 1) (by omega) v).mp hv1) hvv
                  have hF : graphFun G ∅ (pairInput v v) = true := hbel (pairInput v v) hg
                  exact (G.irrefl ((M1528.P2.graphFun_pair G v v).mp hF)).elim
              · -- junk: witness k
                right
                refine ⟨k, (M1528.P1.junk_iff G C k).mpr ⟨hk, hop, hbel⟩, ?_⟩
                intro b
                rcases M1528.P2.fin2_sub b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb]
                · exact hs0
                · exact hs1
            · exact Or.inr h1j
          · exact Or.inr h0j
        · -- OR gate
          rw [M1528.P1.S98.W_or n C _ k hk hop (opnd C k 0) (opnd C k 1) hin (hlt 0) (hlt 1)] at hW
          rw [Bool.or_eq_true] at hW
          rcases hW with h0 | h1
          · have ih0 := ih (opnd C k 0) (hlt 0) (by omega) h0
            rcases ih0 with hr | hj
            · left
              rcases hr with h | h
              · exact Or.inl (Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h)
              · exact Or.inr (Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h)
            · exact Or.inr hj
          · have ih1 := ih (opnd C k 1) (hlt 1) (by omega) h1
            rcases ih1 with hr | hj
            · left
              rcases hr with h | h
              · exact Or.inl (Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h)
              · exact Or.inr (Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hin]; simp⟩ h)
            · exact Or.inr hj
  have hF : circuitFun n C (pairInput p v) = true := by
    rw [hfun]
    exact (M1528.P2.graphFun_pair G p v).mpr hEdge
  have hWout : M1528.P1.S98.W n C (pairInput p v) C.output = true := hF
  have houtlt : C.output < n + C.gates.length := by
    by_contra hge
    push Not at hge
    have hfalse : M1528.P1.S98.W n C (pairInput p v) C.output = false := by
      show (C.wires (List.ofFn (pairInput p v))).getD C.output false = false
      exact M1528.P1.S98.getD_ge_length _ _ (by rw [M1528.P1.S98.wires_length]; exact hge)
    rw [hfalse] at hWout
    exact Bool.false_ne_true hWout
  rcases claim C.output houtlt hWout with h | h
  · rcases h with h | h
    · have hpp : M1528.P1.S98.W n C (pairInput p p) p.val = true := by
        rw [M1528.P1.S98.W_input n C _ p.val p.isLt]
        exact (M1528.P2.pairInput_true p p ⟨p.val, p.isLt⟩).mpr (Or.inl rfl)
      have h2 := M1528.P2.orR_mono n C hAO (pairInput p p) C.output p.val h hpp
      have h3 : circuitFun n C (pairInput p p) = true := h2
      rw [hfun] at h3
      exact (G.irrefl ((M1528.P2.graphFun_pair G p p).mp h3)).elim
    · have hvv : M1528.P1.S98.W n C (pairInput v v) v.val = true := by
        rw [M1528.P1.S98.W_input n C _ v.val v.isLt]
        exact (M1528.P2.pairInput_true v v ⟨v.val, v.isLt⟩).mpr (Or.inl rfl)
      have h2 := M1528.P2.orR_mono n C hAO (pairInput v v) C.output v.val h hvv
      have h3 : circuitFun n C (pairInput v v) = true := h2
      rw [hfun] at h3
      exact (G.irrefl ((M1528.P2.graphFun_pair G v v).mp h3)).elim
  · exact h
