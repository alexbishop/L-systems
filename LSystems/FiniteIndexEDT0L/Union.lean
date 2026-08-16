/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import LSystems.EDT0L.Union
public import LSystems.FiniteIndexEDT0L.Defs

/-!
# Union

See main theorem `Language.isEDT0LOfIndex_union`
-/

@[expose] public section

namespace EDT0LGrammar

@[simp]
lemma filterNonterminals_map_symbol_lhs_length {α V₀ V₁} (s : List (Symbol α V₀)) :
    (filterNonterminals (List.map (Union.map_symbol_lhs (V₁ := V₁)) s)).length =
      (filterNonterminals s).length := by
  induction s with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [List.map_cons, filterNonterminals_cons]
    split <;> rename_i heq <;> split <;> simp [ih, Union.map_symbol_lhs] at ⊢ heq

@[simp]
lemma filterNonterminals_map_symbol_rhs_length {α V₀ V₁} (s : List (Symbol α V₁)) :
    (filterNonterminals (List.map (Union.map_symbol_rhs (V₀ := V₀)) s)).length =
      (filterNonterminals s).length := by
  induction s with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [List.map_cons, filterNonterminals_cons]
    split <;> rename_i heq <;> split <;> simp [ih, Union.map_symbol_rhs] at ⊢ heq

theorem Union.isIndex {α V₀ T₀ V₁ T₁ : Type*}
  (E₀ : EDT0LGrammar α V₀ T₀)
  {k₀} (h₀ : E₀.IsIndex k₀)
  (E₁ : EDT0LGrammar α V₁ T₁)
  {k₁} (h₁ : E₁.IsIndex k₁) :
    (Union E₀ E₁).IsIndex (Nat.max k₀ k₁) := by
  intro w hw
  rw [Union.generates_iff] at hw
  cases hw with
  | init h =>
    subst h
    simp [isIndex_k_geq_one E₀ h₀, isIndex_k_geq_one E₁ h₁]
  | lhs s h1 h2 =>
    subst h1
    simp only [le_sup_iff]
    left
    have h₀ := h₀ _ h2
    simp [h₀]
  | rhs s h1 h2 =>
    subst h1
    simp only [le_sup_iff]
    right
    have h₁ := h₁ _ h2
    simp [h₁]

end EDT0LGrammar

theorem Language.isEDT0LOfIndex_union {α} (L₁ L₂ : Language α) {k₁ k₂}
  (h₁ : L₁.IsEDT0LOfIndex k₁)
  (h₂ : L₂.IsEDT0LOfIndex k₂) :
    (L₁ + L₂).IsEDT0LOfIndex (max k₁ k₂):= by
  have ⟨_, _ , E₁, PP1, P₁⟩ := h₁
  have ⟨_, _ , E₂, PP2, P₂⟩ := h₂
  have h := EDT0LGrammar.Union.defines_union E₁ E₂
  rw [P₁, P₂] at h
  rw [← h]
  refine EDT0LGrammar.isIndex_imp_language_isEDT0LOfIndex (E₁.Union E₂) (max k₁ k₂) ?_
  exact EDT0LGrammar.Union.isIndex E₁ PP1 E₂ PP2

