import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1745_2
    (hUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)), (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (A.card + G.edgeFinset.card + T.card - 1))
    (hLower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (s : ℕ), (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → (7 : ℕ) ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i j : Fin n, G.Adj i j) → (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) → PEqualNP.MetaComplexity.HasCircuitSize n f s → A.card + G.edgeSet.ncard + sInf {t : ℕ | ∃ T : Finset (Fin n), T.card = t ∧ ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T} - 1 ≤ s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro n G A f C hdeg hgirth hIsol hedge hf hFan hEval hMin hRead
  classical
  let tau : ℕ :=
    sInf {t : ℕ | ∃ T : Finset (Fin n), T.card = t ∧ ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T}
  have hTauNe :
      ({t : ℕ | ∃ T : Finset (Fin n), T.card = t ∧ ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T}).Nonempty := by
    refine ⟨Fintype.card (Fin n), Finset.univ, ?_, ?_⟩
    · simp
    · intro a b _
      exact Or.inl (by simp)
  obtain ⟨T, hTcard, hTcov⟩ := Nat.sInf_mem hTauNe
  obtain ⟨u, w, huw⟩ := hedge
  have hex : ∃ i : Fin n, i ∈ T ∧ ∃ j : Fin n, G.Adj i j := by
    rcases hTcov u w huw with h | h
    · exact ⟨u, h, w, huw⟩
    · exact ⟨w, h, u, SimpleGraph.Adj.symm huw⟩
  obtain ⟨i, hiT, j0, hij0⟩ := hex
  have hiA : i ∉ A := hIsol i j0 hij0
  haveI : DecidableRel G.Adj := fun a b => Classical.dec (G.Adj a b)
  let N : Finset (Fin n) := Finset.univ.filter (fun b => G.Adj i b)
  have hNcard : N.card = 3 := by
    have hset : (N : Set (Fin n)) = G.neighborSet i := by
      ext b
      simp [N, SimpleGraph.mem_neighborSet]
    have hcard : N.card = (N : Set (Fin n)).ncard := by
      simp
    rw [hcard, hset, hdeg i hiA]
  let G' : SimpleGraph (Fin n) :=
    { Adj := fun a b => G.Adj a b ∧ a ≠ i ∧ b ≠ i
      symm := ⟨fun a b h => ⟨SimpleGraph.Adj.symm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => G.irrefl h.1⟩ }
  haveI : DecidableRel G'.Adj := fun a b => Classical.dec (G'.Adj a b)
  have hG'edge : ∃ a b : Fin n, G'.Adj a b := by
    have hNne : N.Nonempty := ⟨j0, by simp [N, hij0]⟩
    obtain ⟨b, hbN⟩ := hNne
    have hib : G.Adj i b := (Finset.mem_filter.mp hbN).2
    have hbne : b ≠ i := by
      intro h
      exact G.irrefl (h ▸ hib)
    have hbA : b ∉ A := hIsol b i (SimpleGraph.Adj.symm hib)
    let Nb : Finset (Fin n) := Finset.univ.filter (fun c => G.Adj b c)
    have hNbcard : Nb.card = 3 := by
      have hset : (Nb : Set (Fin n)) = G.neighborSet b := by
        ext c
        simp [Nb, SimpleGraph.mem_neighborSet]
      have hcard : Nb.card = (Nb : Set (Fin n)).ncard := by
        simp
      rw [hcard, hset, hdeg b hbA]
    have hbi : i ∈ Nb := by
      simp [Nb, SimpleGraph.Adj.symm hib]
    have hother : (Nb.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hbi, hNbcard]
      omega
    obtain ⟨c, hc⟩ := hother
    have hcmem := Finset.mem_erase.mp hc
    have hbc : G.Adj b c := (Finset.mem_filter.mp hcmem.2).2
    exact ⟨b, c, hbc, hbne, hcmem.1⟩
  let inc : Finset (Sym2 (Fin n)) := N.image (fun b => s(i, b))
  have hincard : inc.card = 3 := by
    rw [Finset.card_image_of_injective]
    · exact hNcard
    · intro a b hab
      exact Sym2.congr_right.mp hab
  have hinc_sub : inc ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    have hib : G.Adj i b := (Finset.mem_filter.mp hb).2
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hib
  have hG'_sub : G'.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    have he' : e ∈ G'.edgeSet := (SimpleGraph.mem_edgeFinset).mp he
    revert he'
    refine Sym2.ind (fun a b hab => ?_) e
    rw [SimpleGraph.mem_edgeSet] at hab
    have hG : G.Adj a b := hab.1
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hG
  have hdisj : Disjoint inc G'.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    have heG' : s(i, b) ∈ G'.edgeSet := (SimpleGraph.mem_edgeFinset).mp he'
    rw [SimpleGraph.mem_edgeSet] at heG'
    exact heG'.2.1 rfl
  have hunion : inc ∪ G'.edgeFinset = G.edgeFinset := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with h | h
      · exact hinc_sub h
      · exact hG'_sub h
    · intro he
      have heS : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).mp he
      revert heS
      refine Sym2.ind (fun a b hab => ?_) e
      rw [SimpleGraph.mem_edgeSet] at hab
      by_cases hai : a = i
      · subst hai
        have hbN : b ∈ N := by
          simp [N, hab]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hbN, rfl⟩)
      · by_cases hbi : b = i
        · have haN : a ∈ N := by
            have hia : G.Adj i a := by
              rw [← hbi]
              exact SimpleGraph.Adj.symm hab
            simp [N, hia]
          have hs : s(a, b) = s(i, a) := by
            rw [hbi]
            exact Sym2.eq_swap
          rw [hs]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haN, rfl⟩)
        · have hG' : G'.Adj a b := ⟨hab, hai, hbi⟩
          have he' : s(a, b) ∈ G'.edgeFinset := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hG'
          exact Finset.mem_union_right _ he'
  have hesum : G.edgeFinset.card = G'.edgeFinset.card + 3 := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hincard]
    omega
  have htsum : T.card = (T.erase i).card + 1 := (Finset.card_erase_add_one hiT).symm
  have hIsol' : ∀ a b : Fin n, G'.Adj a b → a ∉ A := by
    intro a b hab
    exact hIsol a b hab.1
  have hCov' : ∀ a b : Fin n, G'.Adj a b → a ∈ T.erase i ∨ b ∈ T.erase i := by
    intro a b hab
    have hmem := hTcov a b hab.1
    have ha : a ≠ i := hab.2.1
    have hb : b ≠ i := hab.2.2
    rcases hmem with h | h
    · exact Or.inl (Finset.mem_erase.mpr ⟨ha, h⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hb, h⟩)
  have hUp := hUpper n G' A (T.erase i) hIsol' hG'edge hCov'
  have hfeq : ∀ x : Fin n → Bool,
      f (Function.update x i false) =
        decide ((∃ a ∈ A, x a = true) ∨ ∃ p q : Fin n, G'.Adj p q ∧ x p = true ∧ x q = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [hf (Function.update x i false), decide_eq_true_iff]
    constructor
    · intro h
      rcases h with ⟨a, ha, hxa⟩ | ⟨p, q, hpq, hp, hq⟩
      · have hane : a ≠ i := by
          intro h
          exact hiA (h ▸ ha)
        rw [Function.update_of_ne hane] at hxa
        exact Or.inl ⟨a, ha, hxa⟩
      · have hpne : p ≠ i := by
          intro h
          rw [h, Function.update_self] at hp
          cases hp
        have hqne : q ≠ i := by
          intro h
          rw [h, Function.update_self] at hq
          cases hq
        rw [Function.update_of_ne hpne] at hp
        rw [Function.update_of_ne hqne] at hq
        exact Or.inr ⟨p, q, ⟨hpq, hpne, hqne⟩, hp, hq⟩
    · intro h
      rcases h with ⟨a, ha, hxa⟩ | ⟨p, q, hpq, hp, hq⟩
      · have hane : a ≠ i := by
          intro h
          exact hiA (h ▸ ha)
        refine Or.inl ⟨a, ha, ?_⟩
        rw [Function.update_of_ne hane]
        exact hxa
      · refine Or.inr ⟨p, q, hpq.1, ?_, ?_⟩
        · rw [Function.update_of_ne hpq.2.1]
          exact hp
        · rw [Function.update_of_ne hpq.2.2]
          exact hq
  have hHas : PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update x i false))
      (A.card + G'.edgeFinset.card + (T.erase i).card - 1) := by
    obtain ⟨C0, hF0, hS0, hE0⟩ := hUp
    refine ⟨C0, hF0, hS0, ?_⟩
    intro x
    rw [hE0 x]
    exact (hfeq x).symm
  have hU : A.card + G.edgeSet.ncard + tau - 1 ≤ C.size := by
    have hsize : PEqualNP.MetaComplexity.HasCircuitSize n f C.size :=
      ⟨C, hFan, le_rfl, by intro x; simpa [PEqualNP.MetaComplexity.circuitFun] using congrFun hEval x⟩
    simpa [tau] using hLower n G A f C.size hdeg hgirth hIsol ⟨u, w, huw⟩ hf hsize
  have hen : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_edgeSet]
  have hbound : A.card + G'.edgeFinset.card + (T.erase i).card - 1 + 4 ≤ C.size := by
    have hpos : 1 ≤ G'.edgeFinset.card := by
      obtain ⟨a, b, hab⟩ := hG'edge
      have he : s(a, b) ∈ G'.edgeFinset := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hab
      exact Finset.one_le_card.mpr ⟨s(a, b), he⟩
    omega
  exact ⟨i, hiA, A.card + G'.edgeFinset.card + (T.erase i).card - 1, hbound, hHas⟩

