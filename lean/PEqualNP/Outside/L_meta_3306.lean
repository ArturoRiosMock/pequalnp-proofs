import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Swap an AND of one wire from each side so the `s4` wire comes first. -/
def norm (s3 s4 : Finset ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [] => g
  | GateOp.and, [_] => g
  | GateOp.and, [a, b] => if a ∈ s4 ∧ b ∈ s3 then g else ⟨GateOp.and, [b, a]⟩
  | GateOp.and, _ :: _ :: _ :: _ => g
  | GateOp.or, _ => g
  | GateOp.not, _ => g
  | GateOp.mod _, _ => g
  | GateOp.maj, _ => g

private lemma norm_op (s3 s4 : Finset ℕ) :
    ∀ g : Gate, (norm s3 s4 g).op = g.op
  | ⟨GateOp.and, []⟩ => by simp [norm]
  | ⟨GateOp.and, [_]⟩ => by simp [norm]
  | ⟨GateOp.and, [a, b]⟩ => by
      by_cases h : a ∈ s4 ∧ b ∈ s3 <;> simp [norm, h]
  | ⟨GateOp.and, _ :: _ :: _ :: _⟩ => by simp [norm]
  | ⟨GateOp.or, _⟩ => by simp [norm]
  | ⟨GateOp.not, _⟩ => by simp [norm]
  | ⟨GateOp.mod _, _⟩ => by simp [norm]
  | ⟨GateOp.maj, _⟩ => by simp [norm]

private lemma norm_len (s3 s4 : Finset ℕ) :
    ∀ g : Gate, g.inputs.length = 2 → (norm s3 s4 g).inputs.length = 2
  | ⟨GateOp.and, []⟩, h => by simp at h
  | ⟨GateOp.and, [_]⟩, h => by simp at h
  | ⟨GateOp.and, [a, b]⟩, _ => by
      by_cases hmem : a ∈ s4 ∧ b ∈ s3 <;> simp [norm, hmem]
  | ⟨GateOp.and, _ :: _ :: _ :: _⟩, h => by simp at h
  | ⟨GateOp.or, ins⟩, h => by simp [norm, h]
  | ⟨GateOp.not, ins⟩, h => by simp [norm, h]
  | ⟨GateOp.mod _, ins⟩, h => by simp [norm, h]
  | ⟨GateOp.maj, ins⟩, h => by simp [norm, h]

private lemma norm_mem (s3 s4 : Finset ℕ) :
    ∀ (g : Gate) {i : ℕ}, i ∈ (norm s3 s4 g).inputs → i ∈ g.inputs
  | ⟨GateOp.and, []⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.and, [_]⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.and, [a, b]⟩, _, hi => by
      by_cases hmem : a ∈ s4 ∧ b ∈ s3
      · simpa [norm, hmem] using hi
      · simp [norm, hmem] at hi
        rcases hi with rfl | rfl <;> simp
  | ⟨GateOp.and, _ :: _ :: _ :: _⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.or, _⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.not, _⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.mod _, _⟩, _, hi => by simpa [norm] using hi
  | ⟨GateOp.maj, _⟩, _, hi => by simpa [norm] using hi

private lemma norm_eval (s3 s4 : Finset ℕ) :
    ∀ (g : Gate) (w : List Bool),
      (norm s3 s4 g).op.eval ((norm s3 s4 g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false)
  | ⟨GateOp.and, []⟩, _ => by simp [norm]
  | ⟨GateOp.and, [_]⟩, _ => by simp [norm]
  | ⟨GateOp.and, [a, b]⟩, w => by
      by_cases h : a ∈ s4 ∧ b ∈ s3
      · simp [norm, h]
      · simp [norm, h, GateOp.eval, Bool.and_comm]
  | ⟨GateOp.and, _ :: _ :: _ :: _⟩, _ => by simp [norm]
  | ⟨GateOp.or, _⟩, _ => by simp [norm]
  | ⟨GateOp.not, _⟩, _ => by simp [norm]
  | ⟨GateOp.mod _, _⟩, _ => by simp [norm]
  | ⟨GateOp.maj, _⟩, _ => by simp [norm]

private lemma fold_norm (s3 s4 : Finset ℕ) (gs : List Gate) (x : List Bool) :
    (gs.map (norm s3 s4)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, norm_eval s3 s4 g x, ih]

private lemma getD_lt {α : Type} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private lemma getD_ge {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma norm_and_order (s3 s4 : Finset ℕ) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (hm : a ∈ s3 ∧ b ∈ s4 ∨ a ∈ s4 ∧ b ∈ s3) :
    ∃ p q : ℕ, (norm s3 s4 g).inputs = [p, q] ∧ p ∈ s4 ∧ q ∈ s3 := by
  have hg : g = ⟨GateOp.and, [a, b]⟩ := by
    cases g with
    | mk op ins =>
      cases hop
      cases hin
      rfl
  rw [hg]
  by_cases h : a ∈ s4 ∧ b ∈ s3
  · exact ⟨a, b, by simp [norm, h], h.1, h.2⟩
  · rcases hm with hAB | hBA
    · refine ⟨b, a, ?_, hAB.2, hAB.1⟩
      simp [norm, h]
    · exact absurd hBA h

end PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro n C s3 s4 hAO hAnd
  classical
  let gs := C.gates.map (PEqualNP.Outside.L_meta_3306.norm s3 s4)
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, C.output⟩
  have hlen : gs.length = C.gates.length := by simp [gs]
  have hAO' : PEqualNP.TopForm.IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hop := PEqualNP.Outside.L_meta_3306.norm_op s3 s4 g0
      have hmem := hAO.1 g0 hg0
      rw [hop]
      exact hmem
    · intro j hj i hi
      rw [hlen] at hj
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          PEqualNP.Outside.L_meta_3306.norm s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C', gs]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt (C.gates.map _) j _ (by simpa using hj)]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt C.gates j _ hj]
        simp [List.getElem_map]
      rw [hgate] at hi
      have him := PEqualNP.Outside.L_meta_3306.norm_mem s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) hi
      exact hAO.2.1 j hj i him
    · intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact PEqualNP.Outside.L_meta_3306.norm_len s3 s4 g0 (hAO.2.2 g0 hg0)
  have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval]
    have hw : C'.wires (List.ofFn x) = C.wires (List.ofFn x) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, C', gs]
      exact PEqualNP.Outside.L_meta_3306.fold_norm s3 s4 C.gates (List.ofFn x)
    simp [hw, C']
  refine ⟨C', hAO', ?_, hfun, ?_, ?_, ?_⟩
  · simp [C', gs, PEqualNP.CircuitLowerBounds.Circuit.size, hlen]
  · intro j
    by_cases hj : j < C.gates.length
    · have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          PEqualNP.Outside.L_meta_3306.norm s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C', gs]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt (C.gates.map _) j _ (by simpa [hlen] using hj)]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt C.gates j _ hj]
        simp [List.getElem_map]
      rw [hgate, PEqualNP.Outside.L_meta_3306.norm_op]
    · have hle : C.gates.length ≤ j := Nat.le_of_not_lt hj
      have hlem : gs.length ≤ j := by simpa [hlen] using hle
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [PEqualNP.Outside.L_meta_3306.getD_ge gs j _ hlem,
        PEqualNP.Outside.L_meta_3306.getD_ge C.gates j _ hle]
  · intro j hjor
    by_cases hj : j < C.gates.length
    · have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          PEqualNP.Outside.L_meta_3306.norm s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C', gs]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt (C.gates.map _) j _ (by simpa [hlen] using hj)]
        rw [PEqualNP.Outside.L_meta_3306.getD_lt C.gates j _ hj]
        simp [List.getElem_map]
      have hg : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or := hjor
      rw [hgate]
      cases hrec : PEqualNP.MetaComplexity.NestedCover.gateAt C j with
      | mk op ins =>
        cases op <;> simp_all [PEqualNP.Outside.L_meta_3306.norm]
    · have hle : C.gates.length ≤ j := Nat.le_of_not_lt hj
      have hlem : gs.length ≤ j := by simpa [hlen] using hle
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C']
      rw [PEqualNP.Outside.L_meta_3306.getD_ge gs j _ hlem,
        PEqualNP.Outside.L_meta_3306.getD_ge C.gates j _ hle]
  · intro j hj hop
    have hj0 : j < C.gates.length := by simpa [hlen, C', gs] using hj
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
        PEqualNP.Outside.L_meta_3306.norm s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C', gs]
      rw [PEqualNP.Outside.L_meta_3306.getD_lt (C.gates.map _) j _ (by simpa [hlen] using hj0)]
      rw [PEqualNP.Outside.L_meta_3306.getD_lt C.gates j _ hj0]
      simp [List.getElem_map]
    have hop0 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rw [← PEqualNP.Outside.L_meta_3306.norm_op s3 s4, ← hgate]
      exact hop
    obtain ⟨a, b, hin, hm⟩ := hAnd j hj0 hop0
    obtain ⟨p, q, hinputs, hp, hq⟩ :=
      PEqualNP.Outside.L_meta_3306.norm_and_order s3 s4 (PEqualNP.MetaComplexity.NestedCover.gateAt C j) a b hop0 hin hm
    refine ⟨p, q, ?_, hp, hq⟩
    rw [hgate]
    exact hinputs
