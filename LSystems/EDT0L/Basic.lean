/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs

/-!
# Basic results

This file contains a collection of results that don't fit anywhere else, or are generally useful
for other proofs.
-/

@[expose] public section

@[simp]
lemma List.map_terminal {α V} (u v : List α) :
    u.map (β := Symbol α V) .terminal = v.map .terminal ↔ u = v := by
  refine map_inj_right ?_
  simp

namespace EDT0LGrammar

@[simp]
theorem no_tables_imp_eq_0 {α V T} [IsEmpty T] (E : EDT0LGrammar α V T) : E.language = 0 := by
  ext1 w
  simp only [language_mem_iff, Language.notMem_zero, iff_false]
  intro contra
  unfold Generates Derives at contra
  rw [Relation.reflTransGen_iff_eq_or_transGen] at contra
  obtain contra | contra := contra
  · simp_all
  · cases contra with | single h | tail x h =>
    obtain ⟨t, h⟩ := h
    exact IsEmpty.false t

def zero {α} : EDT0LGrammar α (Fin 1) (Fin 0) where
  initial := 0
  table := fun _ _ ↦ []

lemma zero_language {α} : zero.language = (0 : Language α) := no_tables_imp_eq_0 zero

def one {α} : EDT0LGrammar α (Fin 1) (Fin 1) where
  initial := 0
  table := fun _ _ ↦ []

lemma one_language {α} : one.language = (1 : Language α) := by
  have go {w : List (Symbol α (Fin 1))} (h : one.Generates w) : w = one.initialWord ∨ w = [] := by
    induction h with
    | refl =>
      simp
    | tail x y ih =>
      rename_i a b
      obtain rfl | rfl := ih <;> {
        simp only [Rewrites, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
          List.append_nil, Fin.exists_fin_one, Fin.isValue] at y
        subst b
        right
        rfl }
  ext1 w
  simp only [language_mem_iff, Language.mem_one]
  constructor
  · intro h
    replace h := go h
    obtain h | h := h <;> simp_all
  · intro h
    subst h
    refine derives_single ?_
    simp only [Rewrites, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
      List.append_nil, List.map_nil, Fin.exists_fin_one, Fin.isValue]
    rfl

/-- We note here that `0 : Language α` is the empty language, i.e., the language which contins no
words. -/
theorem language_0_isEDT0L {α} : Language.IsEDT0L (0 : Language α) := ⟨1, 0, zero, zero_language⟩

/-- We note here that `1 : Language α` is the language which only contains the empty word. -/
theorem language_1_isEDT0L {α} : Language.IsEDT0L (1 : Language α) := ⟨1, 1, one, one_language⟩

def getNonterminal? {α V} : Symbol α V → Option V
  | .terminal _ => none
  | .nonterminal v => some v

def filterNonterminals {α V} : List (Symbol α V) → List V := List.filterMap getNonterminal?

@[simp]
lemma filterNonterminals_nil {α V} : filterNonterminals ([] : List (Symbol α V)) = [] := rfl

@[simp]
lemma filterNonterminals_cons {α V} (x : Symbol α V) (xs : List (Symbol α V)) :
    filterNonterminals (x::xs) = 
      match x with
      | .terminal _ => filterNonterminals xs
      | .nonterminal v => v::filterNonterminals xs := by split <;> rfl

@[simp]
lemma filterNonterminals_terminals {α V} (w : List α) :
    filterNonterminals (V := V) (w.map .terminal) = [] := by
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp [ih]

@[simp]
lemma filterNonterminals_append {α V} (x y : List (Symbol α V)) :
    filterNonterminals (x ++ y) = filterNonterminals x ++ filterNonterminals y :=
  List.filterMap_append

lemma filterNonterminals_mem_iff {α V} (v : V) (x : List (Symbol α V)) :
    v ∈ filterNonterminals x ↔ .nonterminal v ∈ x := by
  induction x with
  | nil =>
    simp
  | cons a as ih =>
    simp only [filterNonterminals_cons, List.mem_cons]
    split <;> simp [ih]

@[simp]
lemma filterNonterminals_count {α V} [DecidableEq α] [DecidableEq V]
  (v : V) (x : List (Symbol α V)) :
    (filterNonterminals x).count v = x.count (.nonterminal v) := by
  induction x with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [filterNonterminals_cons, List.count_cons, beq_iff_eq]
    split
    · simpa
    · simpa [List.count_cons]

@[simp]
lemma filterNonterminals_map_nonterminal {α V} (w : List V) :
    filterNonterminals (α := α) (w.map .nonterminal) = w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp]
lemma filterNonterminals_take_nonterminal {α V} (w : List V) (i) :
    filterNonterminals (α := α) (List.take i <| w.map .nonterminal) = w.take i := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons]
    cases i with
    | zero =>
      simp
    | succ i =>
      simp only [List.take_succ_cons, filterNonterminals_cons, List.cons.injEq, true_and] at ⊢ ih
      simp only [List.take_add_one, List.getElem?_map, filterNonterminals_append] at ih
      cases hxs : xs[i]? with
      | none =>
        simp only [hxs, Option.map_none, Option.toList_none, filterNonterminals_nil,
          List.append_nil] at ih
        exact ih
      | some x' =>
        simp only [hxs, Option.map_some, Option.toList_some, filterNonterminals_cons,
          filterNonterminals_nil, List.append_cancel_right_eq] at ih
        exact ih

lemma filterNonterminals_rewriteWord {α V T} (x : List (Symbol α V)) (E : EDT0LGrammar α V T)
  (t : T) :
    filterNonterminals (E.rewriteWord t x) =
      filterNonterminals (E.rewriteWord t ((filterNonterminals x).map .nonterminal)) := by
  induction x with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [rewriteWord_cons, filterNonterminals_append, filterNonterminals_cons]
    split <;> simp [ih]

lemma filterNonterminals_rewriteSymbols {α V T} (x : List (Symbol α V)) (E : EDT0LGrammar α V T)
  (t : T) :
    filterNonterminals (E.rewriteWord t x) =
      filterNonterminals (List.flatMap (E.table t) (filterNonterminals x)) := by
  rw [filterNonterminals_rewriteWord]
  unfold rewriteWord rewriteSymbol
  rw [List.flatMap_map]

@[simp]
lemma filterNonterminals_equivWord {α α' V V'} {equivα : α ≃ α'} {equivV : V ≃ V'}
  (w : List (Symbol α V)) :
    filterNonterminals (equivWord equivα equivV w) = (filterNonterminals w).map equivV := by
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [equivWord_cons, filterNonterminals_cons, ih]
    split <;> split <;> simp_all

@[simp]
lemma filterNonterminals_equivWord_symm {α α' V V'} {equivα : α ≃ α'} {equivV : V ≃ V'}
  (w : List (Symbol α' V')) :
    filterNonterminals ((equivWord equivα equivV).symm w) =
      (filterNonterminals w).map equivV.symm := by
  rw [equivWord_symm]
  exact filterNonterminals_equivWord w

variable {α V T : Type*} {E : EDT0LGrammar α V T}

@[simp]
lemma rewriteWord_nonterminal_mem [BEq (Symbol α V)] [LawfulBEq (Symbol α V)]
  {w : List (Symbol α V)} {v t} :
    .nonterminal v ∈ E.rewriteWord t w ↔
      ∃ (y : V) (_hy : .nonterminal y ∈ w), .nonterminal v ∈ E.table t y := by
  constructor
  · intro h
    induction w with
    | nil =>
      simp only [rewriteWord_nil, List.not_mem_nil] at h
    | cons a as ih =>
      simp only [rewriteWord_cons, List.mem_append] at h
      obtain h | h := h
      · match a with
        | .terminal a =>
          simp only [rewriteSymbol_terminal, List.mem_cons, reduceCtorEq, List.not_mem_nil,
            or_self] at h
        | .nonterminal v =>
          rename_i vv
          exact ⟨v, List.mem_cons_self, Multiset.mem_coe.mp h⟩
      · replace ⟨y, hy, ih⟩ := ih h 
        exact ⟨y, List.mem_cons_of_mem a hy, ih⟩
  · intro h
    replace ⟨y, hy, h⟩ := h
    obtain ⟨r, s, rfl⟩ := List.mem_iff_append.mp hy
    simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, List.mem_append]
    right; left
    exact h

lemma rewriteWord_mem (w : List (Symbol α V)) (x : Symbol α V) (t : T) :
    x ∈ E.rewriteWord t w ↔ ∃ y ∈ w, x ∈ E.rewriteSymbol t y := by
  constructor
  · intro h
    induction w with
    | nil =>
      simp only [rewriteWord_nil, List.not_mem_nil] at h
    | cons a as ih =>
      simp only [rewriteWord_cons, List.mem_append] at h
      obtain h | h := h
      · exact List.exists_mem_cons_of as h
      · exact List.exists_mem_cons_of_exists (ih h)
  · intro h
    replace ⟨y, hy, h⟩ := h
    obtain ⟨r, s, rfl⟩ := List.mem_iff_append.mp hy
    simp only [rewriteWord_append, rewriteWord_cons, List.mem_append]
    right; left
    exact h

end EDT0LGrammar

