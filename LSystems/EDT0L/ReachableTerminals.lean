/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import Mathlib.Data.Fintype.Prod

namespace EDT0LGrammar
variable {α V T : Type*} [finV : Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
variable (E : EDT0LGrammar α V T)

def embed_terminal : α ↪ Symbol α V where
  toFun := fun x ↦ .terminal x
  inj' := by
    unfold Function.Injective
    intro a₁ a₂ h
    simp_all only [Symbol.terminal.injEq]

def embed_nonterminal : V ↪ Symbol α V where
  toFun := fun x ↦ .nonterminal x
  inj' := by
    unfold Function.Injective
    intro a₁ a₂ h
    simp_all only [Symbol.nonterminal.injEq]

abbrev visible_terminals : Finset α :=
  let fin : Fintype (T × V) := instFintypeProd T V;
  Finset.sup
    fin.elems
    fun (h, n) ↦
      let x₁ := E.tables h n;
      let x₂ := x₁.filterMap fun x ↦ match x with | .terminal t => some t | .nonterminal _ => none;
      x₂.toFinset

def visible_symbols : Finset (Symbol α V) :=
  finV.elems.map embed_nonterminal ∪ (E.visible_terminals).map embed_terminal

lemma visible_terminal_imp_visible_symbol (a : α) (h : a ∈ E.visible_terminals) :
    .terminal a ∈ E.visible_symbols := by
  unfold visible_symbols
  apply Finset.mem_union_right
  unfold embed_terminal
  simp_all only [Finset.mem_sup, List.mem_toFinset, List.mem_filterMap, Prod.exists,
    Finset.mem_map_mk]

lemma visible_symbol_imp_visible_terminal (a : α) :
    .terminal a ∈ E.visible_symbols → a ∈ E.visible_terminals := by
  intro h
  unfold visible_symbols at h
  apply Finset.mem_union.mp at h
  cases h
  · exfalso
    rename_i h
    unfold embed_nonterminal at h
    simp_all only [
      Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false, exists_false]
  · rename_i h
    unfold embed_terminal at h
    simp_all only [Finset.mem_map_mk, Finset.mem_sup, List.mem_toFinset, List.mem_filterMap,
      Prod.exists]

@[simp]
lemma visible_symbol_nonterminal (v : V) :
    .nonterminal v ∈ E.visible_symbols := by
  unfold visible_symbols
  apply Finset.mem_union_left
  unfold embed_nonterminal
  simp only [Finset.mem_map_mk]
  exact Fintype.complete v

@[simp]
lemma visible_symbol_tables_visible (t : T) (v : V) :
    ∀ x ∈ E.tables t v, x ∈ E.visible_symbols := by
  intro x h
  match x with
  | .nonterminal n' =>
    exact visible_symbol_nonterminal E n'
  | .terminal a =>
    unfold visible_symbols
    apply Finset.mem_union_right
    unfold visible_terminals
    unfold embed_terminal
    simp only [Finset.mem_map_mk, Finset.mem_sup, List.mem_toFinset, List.mem_filterMap,
      Prod.exists]
    use t, v
    constructor
    · exact Fintype.complete (t, v)
    · use (.terminal a)

end EDT0LGrammar

