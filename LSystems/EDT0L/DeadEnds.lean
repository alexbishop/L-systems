/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar
variable {T N H : Type*} [Fintype H] [Fintype N] (E : EDT0LGrammar T N H)

def HasDeadEnds (𝔇 : Finset N) : Prop :=
  ∀ 𝔡 ∈ 𝔇, ∀ τ : H, ∃ 𝔡' ∈ 𝔇, .nonterminal 𝔡' ∈ E.tables τ 𝔡

def DeadWord (w : List (Symbol T N)) : Prop :=
  ∃ 𝔇 : Finset N, ∃ _ : E.HasDeadEnds 𝔇, ∃ 𝔡 ∈ 𝔇, .nonterminal 𝔡 ∈ w

lemma dead_end_singleton (𝔡 : N) (h : ∀ τ : H, .nonterminal 𝔡 ∈ E.tables τ 𝔡) :
    E.HasDeadEnds {𝔡} :=
  --
  fun n h τ ↦ ⟨n, h, by simp_all only [Finset.mem_singleton]⟩

lemma rewrite_word_dead_end (w : List (Symbol T N)) (τ : H) (𝔇 : Finset N)
  (h₁ : E.HasDeadEnds 𝔇)
  (h₂ : ∃ 𝔡 ∈ 𝔇, .nonterminal 𝔡 ∈ w) :
    ∃ 𝔡' ∈ 𝔇, .nonterminal 𝔡' ∈ E.RewriteWord τ w := by
  replace ⟨𝔡, h₃, h₂⟩ := h₂
  rw [List.mem_iff_getElem] at h₂
  replace ⟨i, h, h₂⟩ := h₂
  have ⟨u, v, h₄⟩ : ∃ u v, w = u ++ [.nonterminal 𝔡] ++ v := by
    use w.take i
    use w.drop (i + 1)
    rw [← h₂]
    simp only [List.take_append_getElem, List.take_append_drop]
  subst h₄
  replace ⟨𝔡', h₁', h₁⟩  := h₁ 𝔡 h₃ τ
  use 𝔡', h₁'
  simp only [EDT0LGrammar.RewriteWord.append]
  conv =>
    arg 1; arg 1; arg 2
    simp [RewriteWord.single]
  simp_all only [
    List.append_assoc, List.cons_append, List.nil_append, List.mem_append, true_or, or_true]

lemma rewrites_dead_end (w w' : List (Symbol T N)) (𝔇 : Finset N)
  (h₁ : E.HasDeadEnds 𝔇)
  (h₂ : ∃ 𝔡 ∈ 𝔇, .nonterminal 𝔡 ∈ w)
  (h₃ : E.Rewrites w w') :
    ∃ 𝔡' ∈ 𝔇, .nonterminal 𝔡' ∈ w' := by
  unfold Rewrites at h₃
  replace ⟨τ, h₃⟩ := h₃
  subst h₃
  exact rewrite_word_dead_end E w τ 𝔇 h₁ h₂

lemma derives_dead_end (w w' : List (Symbol T N)) (𝔇 : Finset N)
  (h₁ : E.HasDeadEnds 𝔇)
  (h₂ : ∃ 𝔡 ∈ 𝔇, .nonterminal 𝔡 ∈ w)
  (h₃ : E.Derives w w') :
    ∃ 𝔡' ∈ 𝔇, .nonterminal 𝔡' ∈ w' := by
  induction h₃ with
  | refl =>
    exact h₂
  | tail ih₁ ih₂ ih₃ =>
    rename_i x y
    exact rewrites_dead_end E x y 𝔇 h₁ ih₃ ih₂

lemma rewrite_dead_word (w : List (Symbol T N)) (τ : H) (h : E.DeadWord w) :
    E.DeadWord (E.RewriteWord τ w) := by
  replace ⟨𝔇, h, h'⟩ := h
  use 𝔇, h
  exact E.rewrite_word_dead_end w τ 𝔇 h h'

lemma rewrites_dead_word (w w' : List (Symbol T N)) (h : E.DeadWord w) (h' : E.Rewrites w w') :
    E.DeadWord w' := by
  replace ⟨𝔇, h₁, h⟩ := h
  use 𝔇, h₁
  exact rewrites_dead_end E w w' 𝔇 h₁ h h'

lemma derives_dead_word (w w' : List (Symbol T N)) (h : E.DeadWord w) (h' : E.Derives w w') :
    E.DeadWord w' := by
  --
  replace ⟨𝔇, h₁, h⟩ := h
  use 𝔇, h₁
  exact derives_dead_end E w w' 𝔇 h₁ h h'

lemma derives_from_dead_word (w : List (Symbol T N)) (h : E.DeadWord w) :
    ∀ w' : List T, ¬(E.Derives w (w'.map .terminal)) := by
  intro w' h'
  replace h' := E.derives_dead_word _ _ h h'
  replace ⟨_, _, 𝔡, _, h''⟩ := h'
  simp_all only [List.mem_iff_getElem,List.getElem_map, reduceCtorEq, List.length_map, exists_false]

end EDT0LGrammar
