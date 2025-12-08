/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import LSystems.EDT0L.Union
import LSystems.FiniteIndexEDT0L.Defs

namespace EDT0LGrammar

namespace UnionData

section helpers
variable {α V₀ V₁ : Type*}

lemma extend_alphabet₀_is_nonterminal (s : Symbol α V₀) :
    SymbolIsNonterminal s = (SymbolIsNonterminal <| @extend_alphabet₀ α V₀ V₁ <| s) := by
  unfold extend_alphabet₀
  split <;> rfl

lemma extend_alphabet₁_is_nonterminal (s : Symbol α V₁) :
    SymbolIsNonterminal s = (SymbolIsNonterminal <| @extend_alphabet₁ α V₀ V₁ <| s) := by
  unfold extend_alphabet₁
  split <;> rfl

lemma extend_alphabet₀_map_count (w : List (Symbol α V₀)) :
    w.countP SymbolIsNonterminal
    = (w.map (@extend_alphabet₀ α V₀ V₁)).countP SymbolIsNonterminal := by
  induction w with
  | nil => simp only [List.countP_nil, List.map_nil]
  | cons α as ih =>
    simp only [List.map_cons, List.countP_cons]
    rw [ih]
    rw [extend_alphabet₀_is_nonterminal]

lemma extend_alphabet₁_map_count (w : List (Symbol α V₁)) :
    w.countP SymbolIsNonterminal
    = (w.map (@extend_alphabet₁ α V₀ V₁)).countP SymbolIsNonterminal := by
  induction w with
  | nil => simp only [List.countP_nil, List.map_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.countP_cons]
    rw [ih]
    rw [extend_alphabet₁_is_nonterminal]

end helpers

variable {α V₀ T₀ V₁ T₁ : Type*} [Fintype V₀] [Fintype T₀] [Fintype V₁] [Fintype T₁]
variable (data : @UnionData α V₀ T₀ V₁ T₁ _ _ _ _)

theorem closed_under_union' {k₁ k₂ : ℕ}
  (h₀ : data.E₀.IsIndex k₁)
  (h₁ : data.E₁.IsIndex k₂) :
    data.grammar.IsIndex (Nat.max k₁ k₂) := by
  --
  unfold IsIndex
  intro w h
  replace h := data.basic_property w h
  obtain rfl | ⟨u, ⟨rfl, h⟩⟩ | ⟨u, ⟨rfl, h⟩⟩ := h
  · calc List.countP SymbolIsNonterminal [Symbol.nonterminal data.grammar.initial]
      _ = 1 := SymbolIsNonterminal_single_nonterminal _
      _ ≤ k₁ := index_at_least_one _ h₀
      _ ≤ Nat.max k₁ k₂ := le_sup_left
  · rw [← extend_alphabet₀_map_count]
    replace h := generates_implies_le_index data.E₀ u h₀ h
    simp only [le_sup_iff, h, true_or]
  · rw [← extend_alphabet₁_map_count]
    replace h := generates_implies_le_index data.E₁ u h₁ h
    simp only [le_sup_iff, h, or_true]

end UnionData

theorem finite_index_closed_under_union {α : Type*} {k₁ k₂ : ℕ} (L₁ L₂ : Language α)
  (h₁ : L₁.IsEDT0LOfIndex k₁)
  (h₂ : L₂.IsEDT0LOfIndex k₂) :
    (L₁ + L₂).IsEDT0LOfIndex (Nat.max k₁ k₂) := by
  have ⟨_, _ , E₁, f₁, P₁⟩ := h₁
  have ⟨_, _ , E₂, f₂, P₂⟩ := h₂
  let union_data := UnionData.mk E₁ E₂
  have h₃ := union_data.defines_union
  have h₄ := union_data.closed_under_union' f₁ f₂
  have ⟨n,m,E',h',P'⟩ := union_data.grammar.fi_edt0l_grammars_generate_fi_edt0l_languages' h₄
  use n, m, E', h'
  rw [P', h₃, P₁, P₂]

end EDT0LGrammar
