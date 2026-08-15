/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import LSystems.EDT0L.RewriteSequence
public import LSystems.EDT0L.Mapped

@[expose] public section

namespace EDT0LGrammar

abbrev visibleα {α V T} (E : EDT0LGrammar α V T) :=
  { a : α // ∃ (t : T) (v : V), .terminal a ∈  E.table t v}

instance {α V T} [Fintype V] [Fintype T] [DecidableEq α]
  (E : EDT0LGrammar α V T) : Fintype E.visibleα where
  elems :=
    Fintype.elems.sup fun (t : T) ↦
    Fintype.elems.sup fun (v : V) ↦
    ((E.table t v).attach.filterMap
      (fun | ⟨.terminal a, h⟩ => some ⟨a, ⟨_,_,h⟩⟩ | ⟨.nonterminal _, _⟩ => none)).toFinset
  complete := by
    intro x
    simp only [Finset.mem_sup, List.mem_toFinset, List.mem_filterMap, List.mem_attach, true_and,
      Subtype.exists]
    have ⟨t,v,h⟩ := x.prop
    exact ⟨t, Fintype.complete _, v, Fintype.complete _, .terminal ↑x, h, rfl⟩

def attach {α V T} (E : EDT0LGrammar α V T) : EDT0LGrammar E.visibleα V T where
  initial := E.initial
  table :=
    fun t v ↦
      (E.table t v).attach.map
        fun | ⟨.terminal a, h⟩ => .terminal ⟨a, ⟨_,_,h⟩⟩ | ⟨.nonterminal v,_⟩ => .nonterminal v

@[simp]
lemma attach_map {α V T} (E : EDT0LGrammar α V T) : Mapped Subtype.val E.attach = E := by
  ext1
  · rfl
  · funext t v
    unfold Mapped attach mapWord
    simp only [List.map_map]
    change let f : _ → _ := _ ; List.map f _ = _
    intro f
    have : f = Subtype.val := by
      subst f
      ext1 x
      simp only [Function.comp_apply]
      split <;> rename_i heq <;> split at heq <;> grind
    rw [this]
    simp

def unattachSymbolWord {α V T} {E : EDT0LGrammar α V T} :
    List (Symbol E.visibleα V) → List (Symbol α V) :=
  List.map (fun | .terminal a => .terminal a.val | .nonterminal v => .nonterminal v)

@[simp]
lemma unattachSymbolWord_initialWord {α V T} {E : EDT0LGrammar α V T} :
    unattachSymbolWord E.attach.initialWord = E.initialWord := rfl

@[simp]
lemma unattachSymbolWord_cons {α V T} {E : EDT0LGrammar α V T}
  {x : Symbol E.visibleα V} {xs : List (Symbol E.visibleα V)} :
    unattachSymbolWord (x::xs) =
      (match x with | .terminal a => .terminal a.val | .nonterminal v => .nonterminal v)
      ::unattachSymbolWord xs := rfl

@[simp]
lemma unattachSymbolWord_nil {α V T} {E : EDT0LGrammar α V T} :
    unattachSymbolWord (E := E) [] = [] := rfl

@[simp]
lemma unattachSymbolWord_append {α V T} {E : EDT0LGrammar α V T}
  {x y : List (Symbol E.visibleα V)} :
    unattachSymbolWord (x ++ y) = unattachSymbolWord x ++ unattachSymbolWord y := List.map_append

lemma unattachSymbolWord_congr {α V T} {E : EDT0LGrammar α V T} {u v : List (Symbol E.visibleα V)}
  (h : unattachSymbolWord u = unattachSymbolWord v) :
    u = v :=
  let rec go :
      (u v : List (Symbol E.visibleα V)) →
      (h : unattachSymbolWord u = unattachSymbolWord v) →
      u = v
    | [],[],_ => rfl
    | a::as, b::bs, h => by
      simp only [unattachSymbolWord_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have R := go as bs h2
      rw [R]
      simp only [List.cons.injEq, and_true]
      split at h1 <;> split at h1
      · simp_all only [Symbol.terminal.injEq]
        exact Subtype.ext h1
      · simp_all
      · simp_all
      · simp_all
    | [], _::_, h => by simp at h
    |  _::_, [], h => by simp at h
  go u v h

@[simp]
lemma unattachSymbolWord_length {α V T} {E : EDT0LGrammar α V T} {w : List (Symbol E.visibleα V)} :
    (unattachSymbolWord w).length = w.length := by
  simp [unattachSymbolWord]

@[simp]
lemma unattachSymbolWord_terminals {α V T} {E : EDT0LGrammar α V T} (w : List E.visibleα) :
    unattachSymbolWord (w.map .terminal) = w.unattach.map .terminal := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [ih]

@[simp]
lemma filterNonterminals_unattachSymbolWord {α V T} {E : EDT0LGrammar α V T}
  (w : List (Symbol E.visibleα V)) :
    filterNonterminals (unattachSymbolWord w) = filterNonterminals w := by
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [unattachSymbolWord_cons, filterNonterminals_cons]
    split <;> rename_i heq <;> split at heq <;> simp_all

lemma attach_rewriteWord {α V T} (E : EDT0LGrammar α V T) (w : List (Symbol α V))
  (w' : List (Symbol E.visibleα V)) (h : w = unattachSymbolWord w') (t : T) :
    E.rewriteWord t w = unattachSymbolWord (E.attach.rewriteWord t w') := by
  subst h
  induction w' with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [unattachSymbolWord_cons, rewriteWord_cons, ih, unattachSymbolWord_append,
      List.append_cancel_right_eq]
    split
    · rfl
    · rename_i v
      unfold attach unattachSymbolWord
      simp only [rewriteSymbol_nonterminal, List.map_map]
      change let f : _ → _ := _ ; _ = List.map f _
      intro f
      have : f = Subtype.val := by
        subst f
        funext x
        simp only [Function.comp_apply]
        split
        · rename_i a heq
          split at heq
          · rename_i a' h'
            simp only [Symbol.terminal.injEq] at ⊢ heq
            subst heq
            rfl
          · rename_i n prop
            simp at ⊢ heq
        · rename_i v heq
          split at heq
          · simp at heq
          · simp only [Symbol.nonterminal.injEq] at ⊢ heq
            exact Eq.symm heq
      rw [this]
      simp

lemma attach_rewriteSeq {α V T} (E : EDT0LGrammar α V T) (w : List (Symbol α V))
  (w' : List (Symbol E.visibleα V)) (h : w = unattachSymbolWord w') (t : List T) :
    E.rewriteSeq t w = unattachSymbolWord (E.attach.rewriteSeq t w') := by
  induction t using List.reverseRecOn with
  | nil =>
    simpa using h
  | append_singleton xs x ih =>
    simp only [rewriteSeq_seq_append, ih, rewriteSeq_seq_cons, rewriteSeq_refl]
    exact attach_rewriteWord E _ _ rfl x

lemma language_eq_attach_language_map_val {α V T} (E : EDT0LGrammar α V T) :
    E.attach.language.map Subtype.val = E.language := by simp [← mapped_language]

end EDT0LGrammar
