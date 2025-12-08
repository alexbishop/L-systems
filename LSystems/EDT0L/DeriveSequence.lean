/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import LSystems.EDT0L.Basic
import LSystems.EDT0L.ReachableTerminals

namespace EDT0LGrammar
variable {α V T : Type*} [Fintype V] [Fintype T] (E : EDT0LGrammar α V T)

def deriveSeq (s : List T) (w : List (Symbol α V)) : List (Symbol α V) :=
  List.foldl (fun w' τ ↦ E.rewriteWord τ w') w s

section DeriveSequence
@[simp]
lemma deriveSeq_refl (w : List (Symbol α V)) : E.deriveSeq [] w = w := rfl

@[simp]
lemma deriveSeq_nil (s : List T) : E.deriveSeq s [] = [] := List.foldl_fixed' (congrFun rfl) s

lemma derives_iff_deriveSeq (w w' : List (Symbol α V)) :
    E.derives w w' ↔ ∃ s : List T, E.deriveSeq s w = w' := by
  --
  constructor
  · intro h
    induction h with
    | refl =>
      use []
      rw [deriveSeq_refl]
    | tail h₁ h₂ h₃ =>
      replace ⟨τ, h₂⟩ := h₂
      replace ⟨s, h₃⟩ := h₃
      use s ++ [τ]
      unfold deriveSeq
      unfold deriveSeq at h₃
      rw [List.foldl_append, h₃, List.foldl_cons, List.foldl_nil]
      exact h₂
  · intro h
    replace ⟨s, h⟩ := h
    induction s using List.reverseRecOn generalizing w w' with
    | nil =>
      rw [deriveSeq_refl] at h
      rw [h]
      exact Relation.ReflTransGen.refl
    | append_singleton as a ih =>
      unfold deriveSeq at h
      rw [List.foldl_append] at h
      change
        let w'' := E.deriveSeq _ _;
        List.foldl _ w'' _ = _
        at h
      extract_lets w'' at h
      replace ih := ih w w''
      unfold w'' at ih
      simp only [forall_const] at ih
      change E.derives _ w'' at ih
      rw [List.foldl_cons, List.foldl_nil] at h
      exact derives_tail ih ⟨a, h⟩

@[simp]
lemma deriveSeq_seq_single (t : T) (w : List (Symbol α V)) :
    E.deriveSeq [t] w = E.rewriteWord t w := rfl

lemma deriveSeq_seq_append_singleton (ts : List T) (t : T) (w : List (Symbol α V)) :
    E.deriveSeq (ts ++ [t]) w = (E.deriveSeq ts w |> E.deriveSeq [t]) := by
  unfold deriveSeq
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma deriveSeq_seq_append (a b : List T) (w : List (Symbol α V)) :
    E.deriveSeq (a ++ b) w = (E.deriveSeq a w |> E.deriveSeq b) := by
  induction b using List.reverseRecOn with
  | nil =>
    simp only [List.append_nil, deriveSeq_refl]
  | append_singleton bs b ih =>
    conv =>
      lhs
      arg 2
      rw [← List.append_assoc]
    rw [deriveSeq_seq_append_singleton]
    rw [deriveSeq_seq_append_singleton]
    rw [ih]

lemma deriveSeq_seq_cons (t : T) (ts : List T) (w : List (Symbol α V)) :
    E.deriveSeq (t::ts) w = (E.rewriteWord t w |> E.deriveSeq ts) := by
  rw [← List.singleton_append,deriveSeq_seq_append, deriveSeq_seq_single]

lemma deriveSeq_cons (s : List T) (w : Symbol α V) (ws : List (Symbol α V)) :
    E.deriveSeq s (w :: ws) = (E.deriveSeq s [w]) ++ (E.deriveSeq s ws) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl, List.cons_append, List.nil_append]
  | append_singleton as a ih =>
    simp only [deriveSeq_seq_append, deriveSeq_seq_single]
    rw [ih]
    simp only [rewriteWord_append]

@[simp]
lemma deriveSeq_append (s : List T) (a b : List (Symbol α V)) :
    E.deriveSeq s (a ++ b) = (E.deriveSeq s a) ++ (E.deriveSeq s b) := by
  induction a with
  | nil =>
    simp only [List.nil_append, deriveSeq_nil]
  | cons a as ih =>
    rw [List.cons_append]
    rw [deriveSeq_cons]
    conv =>
      rhs; lhs
      rw [deriveSeq_cons]
    rw [ih]
    rw [List.append_assoc]

lemma deriveSeq_single_visible [DecidableEq α] [DecidableEq V]
  (t : T) (v : V) (x : Symbol α V) :
    x ∈ E.deriveSeq [t] [.nonterminal v] → x ∈ E.visible_symbols := by
  --
  intro h
  unfold deriveSeq at h
  simp only [List.foldl_cons, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
    List.append_nil, List.foldl_nil] at h
  unfold visible_symbols
  match h₁ : x with
  | .terminal a =>
    apply Finset.mem_union_right
    simp only [Finset.mem_map, Finset.mem_sup, List.mem_toFinset, List.mem_filterMap, Prod.exists]
    use a
    constructor
    · use t, v
      constructor
      · exact Fintype.complete _
      · use (.terminal a)
    · rfl
  | .nonterminal n =>
    apply Finset.mem_union_left
    rw [← h₁]
    unfold embed_nonterminal
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    use n
    constructor
    · exact Fintype.complete n
    · exact Eq.symm h₁

lemma deriveSeq_mem [DecidableEq α] [DecidableEq V]
  (x : Symbol α V)
  (h : x ∈ E.visible_symbols)
  (t : T) :
    ∀ y ∈ E.rewriteSymbol t x, y ∈ E.visible_symbols := by
  match x with
  | Symbol.nonterminal n' =>
    intro y h'
    exact visible_symbol_tables_visible E t n' y h'
  | Symbol.terminal t =>
    intro y h'
    simp only [rewriteSymbol_terminal, List.mem_cons, List.not_mem_nil, or_false] at h'
    rw [h']
    exact h

lemma deriveSeq_visible [DecidableEq α] [DecidableEq V]
  (s : List T) (v : V) (x : Symbol α V) :
    x ∈ E.deriveSeq s [.nonterminal v] → x ∈ E.visible_symbols := by
  --
  intro h
  induction s using List.reverseRecOn generalizing x with
  | nil =>
    simp only [deriveSeq_refl] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rw [h]
    unfold visible_symbols
    apply Finset.mem_union_left
    unfold embed_nonterminal
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    use v
    constructor
    · exact Fintype.complete v
    · rfl
  | append_singleton as a ih =>
    conv at h =>
      left
      rw [deriveSeq_seq_append]
    rw [deriveSeq_seq_single] at h
    have ⟨a', h₁, h₂⟩ := (E.rewriteWord_mem _ _ _).mp h
    replace ih := ih a' h₁
    match a' with
    | .terminal t =>
      simp only [rewriteSymbol_terminal, List.mem_cons, List.not_mem_nil, or_false] at h₂ 
      rw [h₂]
      exact ih
    | .nonterminal n' =>
      exact deriveSeq_mem E (Symbol.nonterminal n') ih a x h₂

lemma deriveSeq_mem_reduce [DecidableEq α] [DecidableEq V]
  (s : List T) (x : Symbol α V) (w) :
    x ∈ E.deriveSeq s w ↔ ∃ x' ∈ w, x ∈ E.deriveSeq s [x'] := by
  constructor
  · intro h
    by_contra contra
    simp only [not_exists, not_and] at contra
    induction w with
    | nil =>
      simp_all only [deriveSeq_nil, List.not_mem_nil]
    | cons a as ih =>
      simp only [deriveSeq_cons E s a as] at h
      simp only [List.mem_append] at h
      cases h
      · rename_i h
        replace contra := contra a (List.mem_cons_self)
        exact contra h
      · rename_i h
        exact ih h (fun y hy ↦ contra y (List.mem_cons_of_mem a hy))
  · intro h
    have ⟨x', h₁, h₂⟩ := h
    have ⟨a,b,h₃⟩ : ∃ a b, w = a ++ [x'] ++ b := by
      let idx? := w.finIdxOf? x'
      cases h₃ : idx?
      · exfalso
        unfold idx? at h₃
        simp only [List.finIdxOf?_eq_none_iff] at h₃
        exact h₃ h₁
      · rename_i i
        unfold idx? at h₃
        simp only [List.finIdxOf?_eq_some_iff, Fin.getElem_fin, ne_eq] at h₃
        have h₄ : w.take i ++ [x'] ++ w.drop (↑i + 1) = w := by
          have ⟨rfl, _⟩ := h₃
          simp only [List.take_append_getElem, List.take_append_drop]
        exact ⟨_, _, h₄.symm⟩
    rw [h₃]
    simp only [List.append_assoc, deriveSeq_append, List.mem_append]
    right; left
    exact h₂

lemma deriveSeq_nonempty {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List α) (s)
  (h : E.deriveSeq s [.nonterminal E.initial] = w.map .terminal) :
    s ≠ [] := by
  by_contra contra
  subst s
  rw [deriveSeq_refl E] at h
  have h₁ : (.nonterminal E.initial : Symbol α V) ∈ [.nonterminal E.initial] :=
    List.mem_singleton.mpr rfl
  rw [h] at h₁
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁


@[simp]
lemma deriveSeq_terminal (t) (x) :
    E.deriveSeq t [.terminal x] = [.terminal x] := by
  induction t using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl]
  | append_singleton as a ih =>
    rw [deriveSeq_seq_append, ih]
    simp only [deriveSeq_seq_single, rewriteWord_cons, rewriteSymbol_terminal, rewriteWord_nil,
      List.append_nil]


end DeriveSequence

section DeriveSequence
variable {α V T V' T' : Type*} [Fintype V] [Fintype T] [Fintype V'] [Fintype T'] 
variable (data : @EquivData α V T V' T' _ _ _ _)

lemma deriveSeq_equiv (t) (w) :
    data.E.deriveSeq t w =
      data.equivWord.symm (
        data.grammar.deriveSeq
          (data.equivTableSeq t)
          (data.equivWord w)) := by
  induction t using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl, EquivData.equivTableSeq_nil, Equiv.symm_apply_apply]
  | append_singleton as a ih =>
    simp only [EquivData.equivTableSeq_append, EquivData.equivTableSeq_cons,
      EquivData.equivTableSeq_nil]
    simp only [deriveSeq_seq_append, ih]
    simp only [deriveSeq_seq_single, EquivData.grammar_rewriteWord_iff, Equiv.symm_apply_apply]

lemma deriveSeq_equiv' (t) (w) :
    data.grammar.deriveSeq t w =
      data.equivWord (
        data.E.deriveSeq
          (data.equivTableSeq.symm t)
          (data.equivWord.symm w)) := by
  induction t using List.reverseRecOn with
  | nil =>
    simp only [deriveSeq_refl, EquivData.equivTableSeq_grammar_nil, Equiv.apply_symm_apply]
  | append_singleton as a ih =>
    simp only [EquivData.equivTableSeq_grammar_append, EquivData.equivTableSeq_grammar_cons,
      EquivData.equivTableSeq_grammar_nil]
    simp only [deriveSeq_seq_append, ih]
    simp only [deriveSeq_seq_single, EquivData.grammar_rewriteWord_iff, Equiv.symm_apply_apply]

end DeriveSequence

end EDT0LGrammar
