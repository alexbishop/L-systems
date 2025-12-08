/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.Defs
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.NormalForm

namespace EDT0LGrammar
namespace LULTImpFiEDT0L

lemma deriveSeq_normalForm {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm w)
  (s : List (annotated_tables E)) :
    normalForm (deriveSeq (E.LULTImpFiEDT0L) s w) := by
  --
  induction s using List.reverseRecOn with
  | nil => exact h
  | append_singleton as a ih =>
    rw [deriveSeq_seq_append, deriveSeq_seq_single]
    exact normalForm_rewrite (E.LULTImpFiEDT0L.deriveSeq as w) ih

lemma deriveSeq_normalForm_ending_final {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm w)
  (s : List (annotated_tables E)) :
    let w' := deriveSeq (E.LULTImpFiEDT0L) (s ++ [.final]) w
    normalForm.deadP w' ∨ normalForm.outputP w' := by
  intro w'
  subst w'
  simp only [deriveSeq_seq_append, deriveSeq_seq_single]
  change
    let w'' := _
    normalForm.deadP (E.LULTImpFiEDT0L.rewriteWord _ w'')
    ∨ normalForm.outputP (E.LULTImpFiEDT0L.rewriteWord _ w'')
  intro w''
  --
  have h₁ : normalForm w'' := by
    subst w''
    exact deriveSeq_normalForm w h s
  --
  cases h₁
  · rename_i h₁
    have h₂ := normalForm_start_rewrite_not_start h₁ (t := .final) (not_eq_of_beq_eq_false rfl)
    left
    use []
    simp only [List.map_nil, List.nil_append]
    exact h₂
  · rename_i h₁
    left
    simp only [normalForm_dead_rewrite, h₁]
  · rename_i h₁
    right
    simp only [normalForm_output_rewrite, h₁]
  · rename_i h₁
    obtain ⟨f, h₁⟩ := h₁
    by_cases h₂ : f = fun _ ↦ .zero
    · subst f
      have ⟨s, hs, h₃⟩ := normalForm_step_rewrite_final₁ _ h₁
      right
      exact ⟨s, h₃⟩
    · have h₃ := normalForm_step_rewrite_final _ h₁ h₂
      left
      exact h₃

lemma deriveSeq_without_final {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (s : List (annotated_tables E))
  (h₁ : normalForm w)
  (h₂ : ¬ normalForm.outputP w)
  (h₃ : .final ∉ s) :
    ¬ normalForm.outputP (deriveSeq (E.LULTImpFiEDT0L) s w) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl]
    exact h₂
  | append_singleton as a ih =>
    have h₃ : .final ∉ as := by
      simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq,
        not_false_eq_true]
    have h₄ : .final ≠ a := by
      simp_all only [not_false_eq_true, forall_const, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, false_or, ne_eq]
    replace ih := ih h₃
    rw [deriveSeq_seq_append, deriveSeq_seq_single]
    --
    have ih' : normalForm (E.LULTImpFiEDT0L.deriveSeq as w) := deriveSeq_normalForm w h₁ as
    --
    cases ih'
    · rename_i ih'
      by_cases h₅ : a = .start
      · subst a
        have h₆ := normalForm_start_rewrite_start ih'
        have h₇ := normalForm_start_rewrite_start' E
        rw [← h₆] at h₇
        exact normalForm_step_imp_not_output E _ h₇
      · have h₆ := normalForm_start_rewrite_not_start ih' h₅
        have h₇ := normalForm_start_rewrite_not_start' E
        rw [← h₆] at h₇
        exact normalForm_dead_imp_not_output E _ h₇
    · rename_i ih'
      have h₅ := normalForm_dead_rewrite _ ih' a
      rw [← h₅] at ih'
      exact normalForm_dead_imp_not_output E _ ih'
    · rename_i ih'
      exfalso
      exact ih ih'
    · rename_i ih'
      obtain ⟨f, ih'⟩ := ih'
      cases a
      · have h₅ := normalForm_step_rewrite_start _ ih'
        exact normalForm_dead_imp_not_output E _ h₅
      · simp only [ne_eq, not_true_eq_false] at h₄
      · rename_i t g
        have h₅ := normalForm_step_rewrite_step _ ih' g t
        split at h₅
        · exact normalForm_step_imp_not_output E _ h₅
        · exact normalForm_dead_imp_not_output E _ h₅

lemma deriveSeq_dead {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w)
  (s : List (annotated_tables E)) :
    normalForm.deadP (deriveSeq (E.LULTImpFiEDT0L) s w) := by
  --
  induction s with
  | nil => exact h
  | cons a as ih =>
    rw [deriveSeq_seq_cons]
    simp only [normalForm_dead_rewrite, h, ih]

lemma deriveSeq_to_non_start {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List (annotated_symbols E))
  (h₁ : normalForm w)
  (h₂ : ¬ normalForm.startP w)
  (s : List (annotated_tables E)) :
    ¬ normalForm.startP (deriveSeq (E.LULTImpFiEDT0L) s w) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl]
    exact h₂
  | append_singleton as a ih =>
    have ih' : normalForm (E.LULTImpFiEDT0L.deriveSeq as w) := deriveSeq_normalForm w h₁ as
    cases ih'
    · rename_i ih'
      exfalso
      exact ih ih'
    · rename_i ih'
      rw [deriveSeq_seq_append, deriveSeq_seq_single]
      have h₁ := normalForm_dead_rewrite _ ih' a
      rw [h₁]
      exact ih
    · rename_i ih'
      rw [deriveSeq_seq_append, deriveSeq_seq_single]
      have h₁ := normalForm_output_rewrite _ ih' a
      rw [h₁]
      exact ih
    · rename_i ih'
      rw [deriveSeq_seq_append, deriveSeq_seq_single]
      obtain ⟨f, ih'⟩ := ih'
      cases a
      · have h₃ := normalForm_step_rewrite_start _ ih'
        exact normalForm_dead_imp_not_start E _ h₃
      · by_cases h₃ : f = fun _ ↦ .zero
        · subst f
          have ⟨s, w', h₃⟩ := normalForm_step_rewrite_final₁ _ ih'
          have h₄ :
            normalForm.outputP
              (E.LULTImpFiEDT0L.rewriteWord .final (E.LULTImpFiEDT0L.deriveSeq as w)) := ⟨s, h₃⟩
          exact normalForm_output_imp_not_start E _ h₄
        · have h₄ := normalForm_step_rewrite_final _ ih' h₃
          exact normalForm_dead_imp_not_start E _ h₄
      · rename_i h' f'
        have h₃ := normalForm_step_rewrite_step _ ih' f' h'
        split at h₃
        · exact normalForm_step_imp_not_start E _ h₃
        · exact normalForm_dead_imp_not_start E _ h₃

lemma deriveSeq_from_output {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w)
  (s : List (annotated_tables E)) :
    deriveSeq (E.LULTImpFiEDT0L) s w = w := by
  --
  induction s using List.reverseRecOn with
  | nil => 
    simp only [deriveSeq_refl]
  | append_singleton as a ih =>
    rw [deriveSeq_seq_append, deriveSeq_seq_single]
    simp only [normalForm_output_rewrite, ih, h]

lemma deriveSeq_from_ouput_is_output {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w)
  (s : List (annotated_tables E)) :
    normalForm.outputP (deriveSeq (E.LULTImpFiEDT0L) s w) := by
  --
  rw [deriveSeq_from_output _ h]
  exact h

lemma deriveSeq_from_step {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f)
  (s : List (annotated_tables E)) :
    let w' := deriveSeq (E.LULTImpFiEDT0L) s w;
    normalForm.outputP w' ∨ (∃ g, normalForm.stepP w' g) ∨ normalForm.deadP w' := by
  --
  induction s using List.reverseRecOn with
  | nil =>
    extract_lets w'
    right; left
    exact Exists.intro f h
  | append_singleton as a ih =>
    extract_lets w'
    extract_lets ih_w' at ih
    obtain ih | ih | ih := ih
    · left
      have h₃ : ih_w' = w' := by
        subst ih_w' w'
        rw [deriveSeq_seq_append, deriveSeq_seq_single]
        exact Eq.symm (normalForm_output_rewrite (E.LULTImpFiEDT0L.deriveSeq as w) ih a)
      rw [← h₃]
      exact ih
    · subst w' ih_w'
      obtain ⟨g, ih⟩ := ih
      cases a
      · have h₁ := normalForm_step_rewrite_start _ ih
        right;right
        rw [deriveSeq_seq_append, deriveSeq_seq_single]
        exact h₁
      · by_cases h₁ : g = fun _ ↦ .zero
        · subst h₁
          have ⟨s, w', h₁⟩ := normalForm_step_rewrite_final₁ _ ih
          have h₂ :
            normalForm.outputP
              (E.LULTImpFiEDT0L.rewriteWord .final (E.LULTImpFiEDT0L.deriveSeq as w)) := ⟨s, h₁⟩
          left
          rw [deriveSeq_seq_append, deriveSeq_seq_single]
          exact h₂
        · have h₂ := normalForm_step_rewrite_final _ ih h₁
          right;right
          rw [deriveSeq_seq_append, deriveSeq_seq_single]
          exact h₂
      · rename_i t g
        have h₁ := normalForm_step_rewrite_step _ ih g t 
        split at h₁
        · right; left
          rw [deriveSeq_seq_append, deriveSeq_seq_single]
          exact Exists.intro g h₁
        · right; right
          rw [deriveSeq_seq_append, deriveSeq_seq_single]
          exact h₁
    · subst w' ih_w'
      have h₁ := normalForm_dead_rewrite _ ih a
      right; right
      rw [deriveSeq_seq_append, deriveSeq_seq_single, h₁]
      exact ih

lemma deriveSeq_start {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (h : E.LULTImpFiEDT0L.generates (w.map .terminal)) :
    ∃ s, E.LULTImpFiEDT0L.deriveSeq ((.start)::s) [.nonterminal .start] = w.map .terminal := by
  have ⟨s,h₁⟩ := (derives_iff_deriveSeq E.LULTImpFiEDT0L [.nonterminal .start] (w.map .terminal)).mp h
  have h₂ : s ≠ [] := by
    intro h₂
    subst s
    rw [deriveSeq_refl E.LULTImpFiEDT0L] at h₁
    --
    have pos : (.nonterminal .start : annotated_symbols E) ∈ [.nonterminal .start] :=
      List.mem_singleton.mpr rfl
    rw [h₁] at pos
    --
    have neg : (.nonterminal .start : annotated_symbols E) ∉ w.map .terminal := by
      simp only [List.mem_map, reduceCtorEq, and_false, exists_false, not_false_eq_true]
    --
    exact neg pos
  --
  have ⟨a,as,h₃⟩ := List.ne_nil_iff_exists_cons.mp h₂
  --
  use as
  --
  obtain ⟨rfl⟩ : a = .start := by
    by_contra h₄
    subst s
    rw [deriveSeq_seq_cons] at h₁
    have h₅ : normalForm.startP (E := E) [.nonterminal .start] := rfl
    have h₆ : 
        normalForm.deadP
          (E.LULTImpFiEDT0L.rewriteWord a [Symbol.nonterminal Nonterminal.start]) := by
      --
      have h₆ := normalForm_start_rewrite_not_start h₅ h₄
      simp only [h₆]
      exact normalForm_start_rewrite_not_start' E
    have h₇ : normalForm.deadP (E := E) (w.map .terminal) := by
      have h₇ := deriveSeq_dead _ h₆ as
      rw [h₁] at h₇
      exact h₇
    obtain ⟨s, h⟩ := h₇
    have h₈ : (.nonterminal .dead : annotated_symbols E) ∈ w.map .terminal := by
      simp only [h, List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false,
        List.mem_cons, List.not_mem_nil, or_false, or_true]
    simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₈
  subst s
  exact h₁

lemma deriveSeq_normal_form₁ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (h : E.LULTImpFiEDT0L.generates (w.map .terminal)) :
    ∃ s,
      (E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ s ++ [.final])
        [.nonterminal .start] = w.map .terminal)
      ∧ (.start ∉ s ∧ .final ∉ s) := by
  have ⟨s,h₁⟩ := deriveSeq_start w h
  -- --
  let idx? := s.finIdxOf? .final
  cases h₂ : idx?
  · subst idx?
    simp only [List.finIdxOf?_eq_none_iff] at h₂
    exfalso
    have h₃ : .final ∉ .start :: s := by
      simp only [List.mem_cons, reduceCtorEq, false_or]
      exact h₂
    have h_neg := deriveSeq_without_final
      [.nonterminal .start] (.start::s) (.start rfl)
      (normalForm_start_imp_not_output E [Symbol.nonterminal Nonterminal.start] rfl) h₃
    rw [h₁] at h_neg
    have h_pos : normalForm.outputP (E := E) (w.map .terminal) := ⟨w, rfl⟩
    exact h_neg h_pos
  · subst idx?
    rename_i i
    simp only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, ne_eq] at h₂
    obtain ⟨h₂_l, h₂_r⟩ := h₂
    --
    have h₃ : s = s.take ↑i ++ [s[↑i]] ++ s.drop (↑i + 1) := by
      simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
    --
    have ⟨a,b,h₄,h₅⟩ : ∃ a b, E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ a ++ [.final] ++ b)
        [.nonterminal .start] = w.map .terminal ∧ .final ∉ a := by
      use (s.take ↑i), (s.drop (↑i + 1))
      constructor
      · rw [← h₂_l]
        conv =>
          lhs
          arg 2
          simp only [List.cons_append, List.nil_append, List.take_append_getElem,
            List.take_append_drop]
        exact h₁
      · intro h₄
        let idx? := (s.take ↑i).finIdxOf? .final
        cases h₅ : idx?
        · subst idx?
          simp only [List.finIdxOf?_eq_none_iff, h₄, not_true_eq_false] at h₅
        · subst idx?
          rename_i j
          simp only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, List.getElem_take, ne_eq] at h₅
          obtain ⟨h₅_l, h₅_r⟩ := h₅

          have h_1 : (s.take i).length = i := by
            simp only [List.length_take, Fin.is_le', inf_of_le_left]
          have h_2 : j < (s.take i).length := by
            simp only [Fin.is_lt]
          have h_3 : i < s.length := by
            simp only [Fin.is_lt]
          --
          simp only [h_1] at h_2
          have h_4 : ↑j < s.length := Nat.lt_trans h_2 h_3

          have h₆ := h₂_r ⟨j, h_4⟩ (Fin.val_fin_lt.mpr h_2)
          simp only at h₆
          exact h₆ h₅_l
    use a
    rw [deriveSeq_seq_append E.LULTImpFiEDT0L] at h₄

    change
      let w' : List (annotated_symbols E) := _
      E.LULTImpFiEDT0L.deriveSeq b w' = _
      at h₄
    extract_lets w' at h₄

    have h₆ := deriveSeq_normalForm_ending_final (E := E)
              [.nonterminal .start]
              (.start rfl)
              ([Table.start] ++ a)
    extract_lets w'' at h₆
    --
    have h₇ : w'' = w' := rfl
    --
    rw [h₇] at h₆
    clear h₇
    --
    subst w'
    
    cases h₆
    · rename_i h₆
      have h₇ := deriveSeq_dead _ h₆ b
      exfalso
      clear * - h₄ h₇
      replace ⟨s, h₇⟩ := h₇
      rw [h₇] at h₄
      clear * - h₄
      have h₁ :
          (.nonterminal .dead : annotated_symbols E)
            ∈ List.map Symbol.terminal s ++ [Symbol.nonterminal Nonterminal.dead] := by
        simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false,
          List.mem_cons, List.not_mem_nil, or_false, or_true]
      rw [h₄] at h₁
      simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁
    · rename_i h₆
      have h₇ := deriveSeq_from_output _ h₆ b
      rw [h₇] at h₄
      use h₄
      constructor
      · by_contra contra
        have ⟨n,m,h₈⟩ : ∃ n m, a = n ++ [.start] ++ m := by
          have ⟨i, h₈⟩ := List.get_of_mem contra
          use (a.take i), (a.drop (↑i + 1))
          rw [← h₈]
          simp only [List.get_eq_getElem, List.take_append_getElem, List.take_append_drop]
        rw [h₈] at h₆
        clear * - h₅ h₆ h₈
        simp only [List.append_assoc] at h₆
        change
          let w := m ++ [.final]
          normalForm.outputP (E.LULTImpFiEDT0L.deriveSeq (_ ++ (_ ++ (_ ++ w))) _)
          at h₆
        extract_lets w at h₆
        simp only [← List.append_assoc] at h₆
        --
        rw [deriveSeq_seq_append] at h₆
        conv at h₆ =>
          arg 1
          arg 3
          rw [deriveSeq_seq_append]
          rw [deriveSeq_seq_append]
        --
        change
          let level0 := [.nonterminal .start]
          let level1 := E.LULTImpFiEDT0L.deriveSeq _ level0
          let level2 := E.LULTImpFiEDT0L.deriveSeq _ level1
          let level3 := E.LULTImpFiEDT0L.deriveSeq _ level2
          let level4 := E.LULTImpFiEDT0L.deriveSeq _ level3
          normalForm.outputP level4
          at h₆
        extract_lets level0 level1 level2 level3 level4 at h₆
        --
        have result₀ : normalForm.startP level0 := rfl
        --
        have result₁ : ∃ g, normalForm.stepP level1 g := by
          subst level1
          rw [deriveSeq_seq_single]
          have h₁ := normalForm_start_rewrite_start result₀
          rw [h₁]
          use fun x ↦ if x = E.initial then .one else .zero
          exact normalForm_start_rewrite_start' E
        --
        have result₂ : 
            normalForm.outputP level2
              ∨ (∃ g, normalForm.stepP level2 g)
              ∨ normalForm.deadP level2 := by
          subst level2
          have ⟨g, result₁⟩ := result₁
          exact deriveSeq_from_step level1 result₁ n
        have result₂' : ¬ normalForm.outputP level2 := by
          subst level2
          rw [h₈] at h₅
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
            List.mem_cons, reduceCtorEq, false_or, not_or] at h₅
          have ⟨h, _⟩ := h₅
          exact deriveSeq_without_final level1 n
            (normalForm.step result₁)
            (by
              obtain ⟨g, h⟩ := result₁
              exact normalForm_step_imp_not_output E level1 h)
            h
        replace result₂ : (∃ g, normalForm.stepP level2 g) ∨ normalForm.deadP level2 := by
          simp_all only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append,
            List.mem_cons, reduceCtorEq, false_or, not_or]
        clear result₂'
        --
        have result₃ : normalForm.deadP level3 := by
          subst level3
          cases result₂
          · rename_i h
            simp only [deriveSeq_seq_single]
            have ⟨f, h'⟩ := h
            have h₁ := normalForm_step_rewrite_start _ h'
            simp only at h₁
            exact h₁
          · rename_i h
            simp only [deriveSeq_seq_single]
            have h₁ := normalForm_dead_rewrite _ h .start
            rw [h₁]
            exact h
        --
        have result₄ : normalForm.deadP level4 := by
          subst level4
          exact deriveSeq_dead level3 result₃ w
        --
        clear * - result₄ h₆
        subst level4 level3 level2 level1 level0
        --
        exact normalForm_dead_imp_not_output E _ result₄ h₆
      · exact h₅

lemma deriveSeq_normal_form₂ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (h : E.LULTImpFiEDT0L.generates (w.map .terminal)) :
    ∃ s : List (H × status_all_nonterminals E),
      E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal := by
  have ⟨s, h₁, h₂, h₃⟩ := deriveSeq_normal_form₁ w h
  --
  let P :
      (n : annotated_tables E) → (h : n ≠ .start ∧ n ≠ .final) → (H × status_all_nonterminals E) :=
    fun n h ↦ 
      match n with
      | .step t n => (t,n)
      | .start => nomatch h
      | .final => nomatch h
  --
  let Q : (H × status_all_nonterminals E) → (annotated_tables E) := fun n ↦ .step n.1 n.2
  --
  let s' : List (H × status_all_nonterminals E) :=
    List.pmap P s
      (by
        intro n h
        constructor <;> intro contra <;> rw [contra] at h
        · exact h₂ h
        · exact h₃ h )
  --
  use s'
  --
  have h₂ : List.map (fun x ↦ Table.step x.1 x.2) s' = s := by
    subst s'
    rw [List.map_pmap]
    change
      let f := _
      have hp := _
      List.pmap f s hp = s
    extract_lets f hp
    --
    have h₁ : ∀ a (h : a ∈ s), f a (hp a h) = a := by
      intro a h
      subst f hp
      cases a
      · exfalso
        exact h₂ h
      · exfalso
        exact h₃ h
      · beta_reduce
        clear * -
        gcongr
    --
    exact List.pmap_eq_self.mpr h₁
  --
  rw [h₂]
  exact h₁

lemma deriveSeq_normal_form₃ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (s : List (H × status_all_nonterminals E))
  (h : E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal) :
    ∀ i (_ : i < s.length),
      let w' :=
        E.LULTImpFiEDT0L.deriveSeq
          ([.start] ++ (s.take (i + 1)).map (fun x ↦ .step x.1 x.2))
          [.nonterminal .start]
      normalForm.stepP w' s[i].2 := by
  intro i h'
  induction i with
  | zero =>
    simp only [zero_add, List.map_take]
    rw [deriveSeq_seq_append, deriveSeq_seq_single]
    have h₁ : normalForm.startP (E := E) [.nonterminal .start] := rfl
    have h₂ := normalForm_start_rewrite_start h₁
    have h₃ := normalForm_start_rewrite_start' E
    --
    rw [h₂]
    --
    have h₄ : s.length ≠ 0 := Nat.ne_zero_of_lt h'
    replace h₄ : s ≠ [] := by exact List.ne_nil_of_length_pos h'
    obtain ⟨a, as, h₄⟩ := List.ne_nil_iff_exists_cons.mp h₄
    simp only [h₄]
    --
    conv =>
      arg 1; arg 2; simp only [List.map_cons, List.take_succ_cons, List.take_zero]
    conv =>
      arg 2; simp only [List.getElem_cons_zero]
    --
    have h₅ := normalForm_step_rewrite_step _ h₃ a.2 a.1
    --
    split at h₅
    · exact h₅
    · exfalso
      rw [← h₂] at h₅
      simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h₅
      --
      have h₆ := deriveSeq_dead _ h₅ (List.drop 1 (s.map fun x ↦ .step x.1 x.2) ++ [.final])
      simp only [← deriveSeq_seq_append] at h₆
      --
      have h₇ : normalForm.outputP
        (E.LULTImpFiEDT0L.deriveSeq
          ([.start] ++ (List.map (fun x ↦ .step x.1 x.2) s) ++ [.final])
          [.nonterminal .start]) := ⟨w, h⟩
      --
      clear * - h₆ h₄ h₇ h'
      --
      change
        let u := _
        normalForm.deadP (E.LULTImpFiEDT0L.deriveSeq u _)
        at h₆
      extract_lets u at h₆
      --
      change
        let v := _
        normalForm.outputP (E.LULTImpFiEDT0L.deriveSeq v _)
        at h₇
      extract_lets v at h₇
      --
      have h₈ : u = v := by
        unfold u v
        simp only [← List.append_assoc]
        simp only [List.append_cancel_right_eq]
        simp only [List.append_assoc]
        simp only [List.append_cancel_left_eq]
        let t := s.map fun x ↦ Table.step x.1 x.2
        have : 0 < t.length := by
          unfold t
          simp only [List.length_map, h']
        --
        have h₈ : [Table.step a.1 a.2] = [t[0]] := by
          unfold t
          simp only [h₄]
          simp only [List.map_cons, List.getElem_cons_zero]
        simp only [h₈]
        unfold t
        rw [List.singleton_append]
        rw [← List.drop_eq_getElem_cons]
        simp only [List.drop_zero]
      --
      rw [h₈] at h₆
      exact normalForm_dead_imp_not_output _ _ h₆ h₇
  | succ i ih =>
    replace ih := ih (Nat.lt_of_succ_lt h')
    simp only at ih
    change
      let s₁ := _
      normalForm.stepP (E.LULTImpFiEDT0L.deriveSeq s₁ _) _
      at ih
    extract_lets s₁ at ih
    simp only
    change
      let s₂ := _
      normalForm.stepP (E.LULTImpFiEDT0L.deriveSeq s₂ _) _
    extract_lets s₂
    --
    let t := List.map (fun x ↦ Table.step x.1 x.2) s
    have len : i + 1 < t.length := by
      unfold t
      simp only [List.length_map, h']
    --
    have h₂ : (Table.step s[i + 1].1 s[i + 1].2) = t[i + 1] := by
      unfold t
      simp only [List.getElem_map]
    --
    have h₁ : s₂ = s₁ ++ [(.step s[i + 1].1 s[i + 1].2)] := by
      subst s₁ s₂
      simp only [List.map_take, List.cons_append, List.nil_append, List.cons.injEq, true_and]
      rw [h₂]
      unfold t
      rw [← List.take_append_getElem]
    rw [h₁, deriveSeq_seq_append, deriveSeq_seq_single]

    have h₁ := normalForm_step_rewrite_step _ ih s[i + 1].2 s[i + 1].1
    split at h₁
    · exact h₁
    · exfalso
      have h₃ := deriveSeq_dead _ h₁
        (List.drop (i + 2) (s.map fun x ↦ Table.step x.1 x.2) ++ [.final])
      unfold s₁ at h₃
      simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h₃
      rw [h₂] at h₃
      unfold t at h₃
      simp only [List.map_take, List.append_assoc] at h₃
      unfold t at len
      conv at h₃ =>
        arg 1
        arg 2
        rhs
        rhs
        rw [← List.append_assoc]
        lhs
        rw [List.singleton_append]
        rw [← List.drop_eq_getElem_cons len]
      conv at h₃ =>
        arg 1
        arg 2
        rhs
        rw [← List.append_assoc]
        lhs
        simp only [List.take_append_drop]
      have h₄ : normalForm.outputP
        (E.LULTImpFiEDT0L.deriveSeq
          ([.start] ++ List.map (fun x ↦ .step x.1 x.2) s ++ [.final])
          [.nonterminal .start]) := ⟨w, h⟩
      exact normalForm_dead_imp_not_output _ _ h₃ h₄

lemma deriveSeq_normal_form₄ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (s : List (H × status_all_nonterminals E))
  (h : E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal) :
    0 < s.length := by
  rw [List.length_pos_iff]
  by_contra contra
  subst s
  simp only [List.map_nil, List.append_nil, List.cons_append, List.nil_append] at h
  unfold deriveSeq LULTImpFiEDT0L at h
  simp only [rewriteSymbol, List.foldl_cons, rewriteWord_cons, rewriteSymbol_nonterminal,
    rewriteWord_nil, List.append_nil, List.nil_append, List.foldl_nil] at h
  split at h
  · rename_i contra
    replace contra := congr_fun contra E.initial
    simp only [↓reduceIte, reduceCtorEq] at contra
  · have h₁ : (.nonterminal .dead : annotated_symbols E) ∈ [.nonterminal .dead] :=
      List.mem_singleton.mpr rfl
    rw [h] at h₁
    simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁

lemma deriveSeq_normal_form₅ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (s : List (H × status_all_nonterminals E))
  (h : E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal) :
    ∀ i (_ : i + 1 < s.length),
      validReplacement s[i].2 s[i+1].2 s[i+1].1 := by
  --
  by_contra contra
  simp only [not_forall] at contra
  --
  obtain ⟨n, hn, contra⟩ := contra
  --
  have h₁ := deriveSeq_normal_form₃ w s h n (Nat.lt_of_succ_lt hn)
  have h₂ := deriveSeq_normal_form₃ w s h (n+1) hn
  --
  simp only at h₁
  simp only [List.take_succ_eq_append_getElem hn] at h₂
  rw [List.map_append, List.map_singleton] at h₂
  --
  have h₃ := normalForm_step_rewrite_step _ h₁ s[n+1].2 s[n+1].1
  --
  split at h₃
  · rename_i h'
    exact contra h'
  · simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h₃
    exact normalForm_dead_imp_not_step _ _ h₃ h₂

lemma deriveSeq_normal_form₆ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (s : List (H × status_all_nonterminals E))
  (h : E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal) :
    have : 0 < s.length := deriveSeq_normal_form₄ w s h
    validReplacement (fun x ↦ if x = E.initial then .one else .zero) s[0].2 s[0].1 := by
  extract_lets h_len
  have h₁ : normalForm.startP (E := E) [.nonterminal .start] := rfl
  have h₂ := normalForm_start_rewrite_start h₁
  have h₃ := normalForm_start_rewrite_start' E
  rw [← h₂] at h₃
  clear h₂
  --
  have h₄ := normalForm_step_rewrite_step _ h₃ s[0].2 s[0].1
  split at h₄
  · rename_i h'
    exact h'
  · have h₅ := deriveSeq_dead _ h₄ ((List.drop 1 (s.map (fun x ↦ .step x.1 x.2))) ++ [.final])
    simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h₅
    --
    let t := List.map (fun x ↦ Table.step x.1 x.2) s
    have len : 0 < t.length := by
      unfold t
      simp only [List.length_map, h_len]
    --
    have h₂ : (Table.step s[0].1 s[0].2) = t[0] := by
      unfold t
      simp only [List.getElem_map]
    --
    simp only [h₂] at h₅
    unfold t at h₅
    --
    conv at h₅ =>
      arg 1
      arg 2
      simp only [List.append_assoc]
      rhs
      rw [← List.append_assoc]
      lhs
      simp only [List.singleton_append, ← List.drop_eq_getElem_cons, List.drop_zero]
    --
    exfalso
    exact normalForm_dead_imp_not_output _ _ h₅ ⟨w, h⟩

lemma deriveSeq_normal_form₇ {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (s : List (H × status_all_nonterminals E))
  (h₁ : 0 < s.length)
  (h₂ : validReplacement (fun x ↦ if x = E.initial then .one else .zero) s[0].2 s[0].1)
  (h₃ : ∀ i (_ : i + 1 < s.length), validReplacement s[i].2 s[i + 1].2 s[i + 1].1) :
    ∀ n (_ : n < s.length),
      normalForm.stepP
        (E.LULTImpFiEDT0L.deriveSeq
          ([.start] ++ List.take (n + 1) (s.map (fun x ↦ .step x.1 x.2)))
          [.nonterminal .start])
        s[n].2
      ∧
      mapByStatus s[n].2
        (E.deriveSeq (List.take (n + 1) (s.map (fun x ↦ x.1))) [.nonterminal E.initial]) =
      deannotateWord
        (E.LULTImpFiEDT0L.deriveSeq
          ([.start] ++ List.take (n + 1) (s.map (fun x ↦ .step x.1 x.2)))
          [.nonterminal .start]) := by
  intro n hn
  induction n with
  | zero =>
    simp only [zero_add, deriveSeq_seq_append, deriveSeq_seq_single]
    have h_1 : normalForm.startP (E := E) [.nonterminal .start] := rfl
    have h_2 := normalForm_start_rewrite_start h_1
    rw [h_2]
    --
    let t := List.map (fun x ↦ x.1) s
    have len : 0 < t.length := by
      unfold t
      simp only [List.length_map, h₁]
    have len2 : t ≠ [] := List.ne_nil_of_length_pos len
    have h_3 : t.take 1 = [t[0]] := by
      rw [List.take_one]
      simp only [List.head?_eq_head len2]
      simp only [Option.toList_some, List.cons.injEq, and_true]
      exact List.head_eq_getElem len2
    unfold t at h_3
    simp only [h_3]
    clear h_3
    --
    let t := List.map (fun x ↦ Table.step x.1 x.2) s
    have len : 0 < t.length := by
      unfold t
      simp only [List.length_map, h₁]
    have len2 : t ≠ [] := List.ne_nil_of_length_pos len
    have h_3 : t.take 1 = [t[0]] := by
      rw [List.take_one]
      simp only [List.head?_eq_head len2]
      simp only [Option.toList_some, List.cons.injEq, and_true]
      exact List.head_eq_getElem len2
    unfold t at h_3
    simp only [h_3]
    clear h_3
    --
    constructor
    · simp only [List.getElem_map, deriveSeq_seq_single]
      have hh := normalForm_start_rewrite_start' E
      have hh' := normalForm_step_rewrite_step _ hh s[0].2 s[0].1
      simp only [↓reduceIte, h₂] at hh'
      exact hh'
    --
    -- have h_4 := normalForm_start_rewrite_start' E
    conv =>
      rhs
      simp only [List.getElem_map, deriveSeq_seq_single, rewriteWord_cons,
        rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil, deannotateWord_append]
      unfold LULTImpFiEDT0L
      simp only [↓reduceIte, rewriteSymbol, deannotateWord_ender, List.append_nil, h₂]
    conv =>
      lhs
      simp only [List.getElem_map, deriveSeq_seq_single, rewriteWord_cons,
        rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil]
    --
    unfold mapByStatus mapByStatusFun deannotateWord deannotateWordFun
    rw [List.filterMap_flatMap, List.filterMap_eq_flatMap_toList]

    change
      let p : _ → _ := _
      let q : _ → _ := _
      List.flatMap p _ = List.flatMap q _
    extract_lets p q
    --
    have hh : ∀ x ∈ E.tables s[0].1 E.initial, p x = q x := by
      intro x hx
      subst p q
      simp only
      cases x
      · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
          List.filterMap_nil]
      · rename_i v
        simp only
        cases hh : s[0].2 v
        · exfalso
          have hh₁ := h₂.nodup_ensure_zero v hh E.initial
          simp only [↓reduceIte, forall_const] at hh₁
          exact hh₁ hx
        · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
            List.filterMap_nil]
        · rename_i ww
          cases ww
          · simp only [Option.toList_none, List.filterMap_nil]
          · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
              List.filterMap_nil]
    --
    rw [List.flatMap_congr hh]
  | succ n ih =>
    have h₃_backup := h₃
    --
    replace ⟨ih', ih⟩ := ih (Nat.lt_of_succ_lt hn)
    replace h₃ := h₃ n hn
    rw [← List.take_append_getElem
      (l := (List.map (fun x ↦ x.1) s))
      (i := n + 1)
      (by simp only [List.length_map, hn]) ]

    rw [← List.take_append_getElem
      (l := List.map (fun x ↦ Table.step x.1 x.2) s)
      (i := n + 1)
      (by simp only [List.length_map, hn]) ]
    --
    constructor
    · simp only [← List.append_assoc]
      rw [deriveSeq_seq_append, deriveSeq_seq_single]
      simp only [List.getElem_map]
      have hh := normalForm_step_rewrite_step _ ih' s[n + 1].2 s[n + 1].1
      simp only [↓reduceIte, h₃_backup] at hh
      exact hh
    --
    conv =>
      args
      · rw [deriveSeq_seq_append, deriveSeq_seq_single]
      · rw [← List.append_assoc, deriveSeq_seq_append, deriveSeq_seq_single]
    --
    change
      let w_edt0l := _
      let w_lult := _
      mapByStatus _ (E.rewriteWord _ w_edt0l) = 
      deannotateWord (E.LULTImpFiEDT0L.rewriteWord _ w_lult)
    extract_lets w_edt0l w_lult
    simp only [List.getElem_map]

    have hh : mapByStatus s[n].2 w_edt0l = deannotateWord w_lult := by
      unfold w_edt0l w_lult
      exact ih
    have hh₁ : normalForm.stepP w_lult s[n].2 := by
      unfold w_lult
      replace h₃ := h₃_backup n hn
      exact ih'

    exact rewrite_agrees w_edt0l w_lult hh₁ h₃ ih

lemma deriveSeq_normal_form₈ {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List α)
  (s : List (T × status_all_nonterminals E))
  (h : E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (s.map (fun x ↦ .step x.1 x.2)) ++ [.final])
        [.nonterminal .start] = w.map .terminal) :
    E.deriveSeq (s.map fun x ↦ x.1) [.nonterminal E.initial] = w.map .terminal := by
  have h₁ := deriveSeq_normal_form₄ _ _ h
  have h₂ := deriveSeq_normal_form₆ _ _ h
  have h₃ := deriveSeq_normal_form₅ _ _ h
  --
  have ⟨h_l, h_r⟩ := deriveSeq_normal_form₇ _ h₁ h₂ h₃ (s.length - 1) (Nat.sub_one_lt_of_lt h₁)
  --
  rw [Nat.sub_one_add_one_eq_of_pos h₁] at h_r
  --
  have h₁' : (List.map (fun x ↦ Table.step x.1 x.2) s).length = s.length := by
    simp only [List.length_map]
  conv at h_l => lhs ;  simp only [← h₁']
  --
  have h₁'' := h₁
  rw [← h₁'] at h₁''
  --
  rw [Nat.sub_one_add_one_eq_of_pos h₁'', List.take_length] at h_l
  --
  have h₄ : s[s.length - 1].2 = fun _ ↦ .zero := by
    by_contra contra
    have hh := normalForm_step_rewrite_final _ h_l contra
    simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at hh
    have hh' : normalForm.outputP
      (E.LULTImpFiEDT0L.deriveSeq
        ([.start] ++ (List.map (fun x ↦ .step x.1 x.2) s) ++ [.final])
      [Symbol.nonterminal Nonterminal.start]) := ⟨w, h⟩
    clear * - hh hh'
    exact normalForm_dead_imp_not_output _ _ hh hh'
  simp only [h₄] at h_l
  simp only [h₄] at h_r
  --
  have ⟨w', h_l', h_l''⟩ := normalForm_step_rewrite_final₁ _ h_l
  --
  obtain rfl : w' = w := by
    simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h_l''
    rw [h_l''] at h
    clear * - h
    let rec proof_imp (w' w : List α)
      (h : (List.map .terminal w' : List (annotated_symbols E)) = List.map .terminal w) :
        w' = w := by
      match w', w with
      | .nil, .nil => rfl
      | a::as, b::bs =>
        simp only [List.map_cons, List.cons.injEq, Symbol.terminal.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain rfl := proof_imp as bs h
        rfl
      | a::as, .nil =>
        simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
      | .nil, a::as =>
        simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
    exact proof_imp w' w h
  conv at h_r =>
    rhs
    rw [← h₁', List.take_length, h_l']
  clear * - h_r
  simp only [mapByStatus_zero, deannotateWord_append, deannotateWord_terminals,
    deannotateWord_ender, List.append_nil] at h_r
  --
  have h : s.length = (List.map (fun x ↦ x.1) s).length := by
    simp only [List.length_map]
  rw [h] at h_r
  --
  rw [List.take_length] at h_r
  exact h_r

end LULTImpFiEDT0L
end EDT0LGrammar
