/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar
variable {α V T : Type*} [Fintype V] [Fintype T] (E : EDT0LGrammar α V T)

def HasDeadEnds (dead : Finset V) : Prop :=
  ∀ 𝔡 ∈ dead, ∀ t : T, ∃ 𝔡' ∈ dead, .nonterminal 𝔡' ∈ E.tables t 𝔡

def DeadWord (w : List (Symbol α V)) : Prop :=
  ∃ dead : Finset V, ∃ _ : E.HasDeadEnds dead, ∃ 𝔡 ∈ dead, .nonterminal 𝔡 ∈ w

lemma dead_end_singleton (𝔡 : V) (h : ∀ t : T, .nonterminal 𝔡 ∈ E.tables t 𝔡) :
    E.HasDeadEnds {𝔡} :=
  --
  fun n h τ ↦ ⟨n, h, by simp_all only [Finset.mem_singleton]⟩

lemma rewrite_word_dead_end (w : List (Symbol α V)) (t : T) (dead : Finset V)
  (h₁ : E.HasDeadEnds dead)
  (h₂ : ∃ 𝔡 ∈ dead, .nonterminal 𝔡 ∈ w) :
    ∃ 𝔡' ∈ dead, .nonterminal 𝔡' ∈ E.rewriteWord t w := by
  replace ⟨𝔡, h₃, h₂⟩ := h₂
  rw [List.mem_iff_getElem] at h₂
  replace ⟨i, h, h₂⟩ := h₂
  have ⟨u, v, h₄⟩ : ∃ u v, w = u ++ [.nonterminal 𝔡] ++ v := by
    use w.take i
    use w.drop (i + 1)
    rw [← h₂]
    simp only [List.take_append_getElem, List.take_append_drop]
  subst h₄
  replace ⟨𝔡', h₁', h₁⟩  := h₁ 𝔡 h₃ t
  use 𝔡', h₁'
  simp only [EDT0LGrammar.rewriteWord_append]
  conv =>
    arg 1; arg 1; arg 2
    simp only [rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
      List.append_nil]
  simp_all only [
    List.append_assoc, List.cons_append, List.nil_append, List.mem_append, true_or, or_true]

lemma rewrites_dead_end (w w' : List (Symbol α V)) (dead : Finset V)
  (h₁ : E.HasDeadEnds dead)
  (h₂ : ∃ 𝔡 ∈ dead, .nonterminal 𝔡 ∈ w)
  (h₃ : E.rewrites w w') :
    ∃ 𝔡' ∈ dead, .nonterminal 𝔡' ∈ w' := by
  unfold rewrites at h₃
  replace ⟨τ, h₃⟩ := h₃
  subst h₃
  exact rewrite_word_dead_end E w τ dead h₁ h₂

lemma derives_dead_end (w w' : List (Symbol α V)) (dead : Finset V)
  (h₁ : E.HasDeadEnds dead)
  (h₂ : ∃ 𝔡 ∈ dead, .nonterminal 𝔡 ∈ w)
  (h₃ : E.derives w w') :
    ∃ 𝔡' ∈ dead, .nonterminal 𝔡' ∈ w' := by
  induction h₃ with
  | refl =>
    exact h₂
  | tail ih₁ ih₂ ih₃ =>
    rename_i x y
    exact rewrites_dead_end E x y dead h₁ ih₃ ih₂

lemma rewrite_dead_word (w : List (Symbol α V)) (t : T) (h : E.DeadWord w) :
    E.DeadWord (E.rewriteWord t w) := by
  replace ⟨𝔇, h, h'⟩ := h
  use 𝔇, h
  exact E.rewrite_word_dead_end w t 𝔇 h h'

lemma rewrites_dead_word (w w' : List (Symbol α V)) (h : E.DeadWord w) (h' : E.rewrites w w') :
    E.DeadWord w' := by
  replace ⟨𝔇, h₁, h⟩ := h
  use 𝔇, h₁
  exact rewrites_dead_end E w w' 𝔇 h₁ h h'

lemma derives_dead_word (w w' : List (Symbol α V)) (h : E.DeadWord w) (h' : E.derives w w') :
    E.DeadWord w' := by
  --
  replace ⟨𝔇, h₁, h⟩ := h
  use 𝔇, h₁
  exact derives_dead_end E w w' 𝔇 h₁ h h'

lemma derives_from_dead_word (w : List (Symbol α V)) (h : E.DeadWord w) :
    ∀ w' : List α, ¬(E.derives w (w'.map .terminal)) := by
  intro w' h'
  replace h' := E.derives_dead_word _ _ h h'
  replace ⟨_, _, 𝔡, _, h''⟩ := h'
  simp_all only [List.mem_iff_getElem,List.getElem_map, reduceCtorEq, List.length_map, exists_false]

end EDT0LGrammar
