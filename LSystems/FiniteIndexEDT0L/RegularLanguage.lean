/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import LSystems.EDT0L.RegularLanguage
import LSystems.FiniteIndexEDT0L.Defs

namespace EDT0LGrammar

lemma terminal_word_count {α V : Type*} (w : List α) :
    List.countP (@SymbolIsNonterminal α V) (List.map .terminal w) = 0 := by
  induction w with
  | nil =>
    simp only [List.map_nil, List.countP_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.countP_cons]
    conv =>
      lhs ; rhs
      unfold SymbolIsNonterminal
      change 0
    simp only [add_zero]
    exact ih

theorem regular_languages_are_fi_edt0l {α : Type*} [Fintype α] (L : Language α) :
    L.IsRegular → L.IsEDT0LOfIndex 1 := by
  unfold Language.IsRegular
  intro h
  have ⟨ _, _, M, h₁ ⟩ := h
  --
  let data := DFAData.mk M
  have h₂ := data.languages_are_identical

  let E := data.grammar

  have h₃ : E.language = M.accepts := by
    unfold EDT0LGrammar.language
    unfold DFA.accepts
    unfold DFA.acceptsFrom
    subst h₁
    simp_all only [exists_const_iff, data, E]

  rw [h₁] at h₃
  rw [← h₃]
  apply E.fi_edt0l_grammars_generate_fi_edt0l_languages'
  
  intro w h
  replace ⟨u, h⟩ := data.generated_words w h
  cases h with
  | inl h =>
    replace h := h.left
    subst h
    rw [terminal_word_count]
    simp only [zero_le]
  | inr h =>
    subst h
    simp only [List.countP_append, terminal_word_count, zero_add]
    unfold SymbolIsNonterminal
    simp only [List.countP_singleton]
    split 
    · rfl
    · simp only [zero_le]

end EDT0LGrammar

