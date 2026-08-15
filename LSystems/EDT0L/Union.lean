/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs

/-!
# EDT0L languages are closed under union

This file provides a constructive proof that the family of EDT0L languages is closed under taking
unions.

## Main definition

* `EDT0LGrammar.Union E_l E_r`: an EDT0L grammar whose language is the union of the languages of
  `E_l` and `E_r`.

## Main theorem

* `EDT0LGrammar.Union.defines_union`: the above definition does precicely what is expected.
* `Language.isEDT0L_union`: the union of two EDT0L languages is EDT0l.
-/

@[expose] public section

namespace EDT0LGrammar
inductive Union.extended_nonterminals (V₀ V₁ : Type*) where
  | lhs (v : V₀)
  | rhs (v : V₁)
  | init
deriving Fintype, DecidableEq

inductive Union.extended_tables (T₀ T₁ : Type*) where
  | lhs (v : T₀)
  | rhs (v : T₁)
  | init_lhs
  | init_rhs
deriving Fintype, DecidableEq

abbrev Union.map_symbol_lhs {α V₀ V₁ : Type*} : Symbol α V₀ → Symbol α (extended_nonterminals V₀ V₁)
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (.lhs n)

abbrev Union.map_symbol_rhs {α V₀ V₁ : Type*} : Symbol α V₁ → Symbol α (extended_nonterminals V₀ V₁)
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (.rhs n)

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
def Union : EDT0LGrammar α (Union.extended_nonterminals V₀ V₁) (Union.extended_tables T₀ T₁) where
  initial := .init
  table := fun
    | .lhs t₀, .lhs v₀ => List.map Union.map_symbol_lhs (E₀.table t₀ v₀)
    | .rhs t₁, .rhs v₁ => List.map Union.map_symbol_rhs (E₁.table t₁ v₁) 
    | .init_lhs, .init => [ .nonterminal <| .lhs E₀.initial ]
    | .init_rhs, .init => [ .nonterminal <| .rhs E₁.initial ] 
    | _, v => [.nonterminal v]

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
@[simp]
lemma Union.rewriteSymbol_lhs (t s) :
    (Union E₀ E₁).rewriteSymbol t (Union.map_symbol_lhs s) =
      match t with
      | .lhs t' =>
        List.map Union.map_symbol_lhs (E₀.rewriteSymbol t' s)
      | .rhs _ | .init_lhs | .init_rhs =>
        [Union.map_symbol_lhs s]
    := by
  match t with
  | .lhs t' =>
    unfold Union rewriteSymbol
    simp only
    match s with
    | .terminal _ =>
      simp only [List.map_cons, List.map_nil]
    | .nonterminal _ =>
      simp only
  | .rhs _ | .init_lhs | .init_rhs =>
    unfold Union rewriteSymbol
    simp only
    match s with | .terminal _ | .nonterminal _ => simp only

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
@[simp]
lemma Union.rewriteSymbol_rhs (t s) :
    (Union E₀ E₁).rewriteSymbol t (Union.map_symbol_rhs s) =
      match t with
      | .rhs t' =>
        List.map Union.map_symbol_rhs (E₁.rewriteSymbol t' s)
      | .lhs _ | .init_lhs | .init_rhs =>
        [Union.map_symbol_rhs s]
    := by
  match t with
  | .rhs t' =>
    unfold Union rewriteSymbol
    simp only
    match s with
    | .terminal _ =>
      simp only [List.map_cons, List.map_nil]
    | .nonterminal _ =>
      simp only
  | .lhs _ | .init_lhs | .init_rhs =>
    unfold Union rewriteSymbol
    simp only
    match s with | .terminal _ | .nonterminal _ => simp only

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
@[simp]
lemma Union.rewritWord_lhs (t w) :
    (Union E₀ E₁).rewriteWord t (List.map Union.map_symbol_lhs w) =
      match t with
      | .lhs t' =>
        List.map Union.map_symbol_lhs (E₀.rewriteWord t' w)
      | .rhs _ | .init_lhs | .init_rhs =>
        List.map Union.map_symbol_lhs w
    := by
  match t with
  | .lhs t' =>
    simp only
    induction w with
    | nil =>
      rfl
    | cons x xs ih =>
      simp only [List.map_cons, rewriteWord_cons, rewriteSymbol_lhs, List.map_append, ih]
  | .rhs _ | .init_lhs | .init_rhs =>
    simp only
    induction w with
    | nil =>
      rfl
    | cons x xs ih =>
      simp only [List.map_cons, rewriteWord_cons, rewriteSymbol_lhs, List.cons_append,
        List.nil_append, ih]

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
@[simp]
lemma Union.rewritWord_rhs (t w) :
    (Union E₀ E₁).rewriteWord t (List.map Union.map_symbol_rhs w) =
      match t with
      | .rhs t' =>
        List.map Union.map_symbol_rhs (E₁.rewriteWord t' w)
      | .lhs _ | .init_lhs | .init_rhs =>
        List.map Union.map_symbol_rhs w
    := by
  match t with
  | .rhs t' =>
    simp only
    induction w with
    | nil =>
      rfl
    | cons x xs ih =>
      simp only [List.map_cons, rewriteWord_cons, rewriteSymbol_rhs, List.map_append, ih]
  | .lhs _ | .init_lhs | .init_rhs =>
    simp only
    induction w with
    | nil =>
      rfl
    | cons x xs ih =>
      simp only [List.map_cons, rewriteWord_cons, rewriteSymbol_rhs, List.cons_append,
        List.nil_append, ih]

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
inductive Union.generatesP (w : List (Symbol α (Union.extended_nonterminals V₀ V₁))) : Prop where
  | init (h : w = [.nonterminal .init])
  | lhs (s) (h₁ : w = List.map Union.map_symbol_lhs s) (h₂ : E₀.Generates s)
  | rhs (s) (h₁ : w = List.map Union.map_symbol_rhs s) (h₂ : E₁.Generates s)

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
lemma Union.generates_iff (w) : (Union E₀ E₁).Generates w ↔ Union.generatesP E₀ E₁ w := by
  constructor
  · intro h
    induction h with
    | refl =>
      exact .init rfl
    | tail x y ih =>
      rename_i u v
      obtain ⟨t, rfl⟩ := y
      cases ih with
      | init ih =>
        subst ih
        cases t with
        | init_lhs =>
          exact generatesP.lhs E₀.initialWord rfl (generates_initial E₀)
        | init_rhs =>
          exact generatesP.rhs E₁.initialWord rfl (generates_initial E₁)
        | lhs t | rhs t =>
          exact .init rfl
      | lhs s h₁ h₂ =>
        subst h₁
        refine generatesP.lhs
          (match t with | .lhs t => E₀.rewriteWord t s | _ => s)
          ?_ ?_
        · simp only [rewritWord_lhs]
          cases t <;> rfl
        · split
          · rename_i ht t
            exact generates_rewriteWord_tail h₂ t
          · exact h₂
      | rhs s h₁ h₂ =>
        subst h₁
        refine generatesP.rhs
          (match t with | .rhs t => E₁.rewriteWord t s | _ => s)
          ?_ ?_
        · simp only [rewritWord_rhs]
          cases t <;> rfl
        · split
          · rename_i ht t
            exact generates_rewriteWord_tail h₂ t
          · exact h₂
  · intro h
    cases h with
    | init h =>
      subst h
      exact (Union E₀ E₁).generates_initial
    | lhs s h₁ h₂ =>
      subst h₁
      induction h₂ with
      | refl =>
        exact derives_single ⟨.init_lhs, rfl⟩
      | tail x y ih =>
        refine derives_tail ih ?_
        obtain ⟨t, rfl⟩ := y
        use .lhs t
        simp only [rewritWord_lhs]
    | rhs s h₁ h₂ =>
      subst h₁
      induction h₂ with
      | refl =>
        exact derives_single ⟨.init_rhs, rfl⟩
      | tail x y ih =>
        refine derives_tail ih ?_
        obtain ⟨t, rfl⟩ := y
        use .rhs t
        simp only [rewritWord_rhs]

variable {α V₀ T₀ V₁ T₁ : Type*} (E₀ : EDT0LGrammar α V₀ T₀) (E₁ : EDT0LGrammar α V₁ T₁) in
theorem Union.defines_union : (Union E₀ E₁).language = E₀.language + E₁.language := by
  ext1 w
  rw [language_mem_iff, Language.mem_add]
  constructor
  · intro h
    rw [generates_iff] at h
    cases h with
    | init h =>
      simp only [List.map_eq_singleton_iff, reduceCtorEq, and_false, exists_false] at h
    | lhs s h₁ h₂ =>
      left
      obtain rfl : s = List.map .terminal w := by
        clear h₂
        induction w generalizing s with
        | nil =>
          simp only [List.map_nil, List.nil_eq, List.map_eq_nil_iff] at h₁
          subst h₁
          rfl
        | cons x y ih =>
          simp only [List.map_cons] at h₁
          replace h₁ := Eq.symm h₁
          rw [List.map_eq_cons_iff] at h₁
          obtain ⟨a, as, rfl, h3,h4⟩ := h₁
          simp only [List.map_cons, List.cons.injEq]
          split_ands
          · unfold map_symbol_lhs at h3
            split at h3
            · simp only [Symbol.terminal.injEq] at h3
              subst h3
              rfl
            · simp only [reduceCtorEq] at h3
          · exact ih as (Eq.symm h4)
      exact (language_mem_iff E₀).mpr h₂
    | rhs s h₁ h₂ =>
      right
      obtain rfl : s = List.map .terminal w := by
        clear h₂
        induction w generalizing s with
        | nil =>
          simp only [List.map_nil, List.nil_eq, List.map_eq_nil_iff] at h₁
          subst h₁
          rfl
        | cons x y ih =>
          simp only [List.map_cons] at h₁
          replace h₁ := Eq.symm h₁
          rw [List.map_eq_cons_iff] at h₁
          obtain ⟨a, as, rfl, h3,h4⟩ := h₁
          simp only [List.map_cons, List.cons.injEq]
          split_ands
          · unfold map_symbol_rhs at h3
            split at h3
            · simp only [Symbol.terminal.injEq] at h3
              subst h3
              rfl
            · simp only [reduceCtorEq] at h3
          · exact ih as (Eq.symm h4)
      exact (language_mem_iff E₁).mpr h₂
  · intro h
    rw [generates_iff]
    obtain h | h := h
    · exact .lhs
        (List.map .terminal w)
        (by simp only [List.map_map, List.map_inj_left, Function.comp_apply, implies_true])
        ((language_mem_iff E₀).mp h)
    · exact .rhs
        (List.map .terminal w)
        (by simp only [List.map_map, List.map_inj_left, Function.comp_apply, implies_true])
        ((language_mem_iff E₁).mp h)

end EDT0LGrammar

theorem Language.isEDT0L_union {α} (L₁ L₂ : Language α)
  (h₁ : L₁.IsEDT0L)
  (h₂ : L₂.IsEDT0L) :
    (L₁ + L₂).IsEDT0L := by
  have ⟨_, _ , E₁, P₁⟩ := h₁
  have ⟨_, _ , E₂, P₂⟩ := h₂
  have h := EDT0LGrammar.Union.defines_union E₁ E₂
  have ⟨n, m, E', P'⟩ := (EDT0LGrammar.Union E₁ E₂).language_isEDT0L
  use n, m, E'
  rw [P', h, P₁, P₂]

