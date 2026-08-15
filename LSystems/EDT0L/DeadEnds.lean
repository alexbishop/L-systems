/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs

@[expose] public section

namespace EDT0LGrammar

def IsDeadEndSet {α V T} (E : EDT0LGrammar α V T) (dead : Set V) : Prop :=
  ∀ 𝔡 ∈ dead, ∀ t : T, ∃ 𝔡' ∈ dead, .nonterminal 𝔡' ∈ E.table t 𝔡

def IsDeadEndSingleton {α V T} (E : EDT0LGrammar α V T) (𝔡 : V) : Prop := E.IsDeadEndSet {𝔡}

def IsDeadWord {α V T} (E : EDT0LGrammar α V T) (w : List (Symbol α V)) : Prop :=
  ∃ (dead : Set V) (_ : E.IsDeadEndSet dead) (𝔡 : V) (_ : 𝔡 ∈ dead), .nonterminal 𝔡 ∈ w

lemma isDeadEndSingleton_iff_isDeadEndSet {α V T} {E : EDT0LGrammar α V T} {𝔡 : V} :
    E.IsDeadEndSingleton 𝔡 ↔ E.IsDeadEndSet {𝔡} := by rfl

lemma isDeadEndSingleton_iff {α V T} (E : EDT0LGrammar α V T) (𝔡 : V) :
    E.IsDeadEndSingleton 𝔡 ↔ ∀ t : T, .nonterminal 𝔡 ∈ E.table t 𝔡 := by
  unfold IsDeadEndSingleton IsDeadEndSet
  simp

lemma rewriteWord_dead_word {α V T} (E : EDT0LGrammar α V T) (w : List (Symbol α V))
  (h : E.IsDeadWord w) (t : T) :
    E.IsDeadWord (E.rewriteWord t w) := by
  replace ⟨dead, h, 𝔡, h', h''⟩ := h
  use dead, h
  rw [List.mem_iff_append] at h''
  obtain ⟨u, v, rfl⟩ := h''
  simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, List.mem_append,
    exists_prop]
  replace ⟨𝔡', h𝔡', h⟩ := h 𝔡 h' t
  use 𝔡', h𝔡'
  right; left
  exact h

lemma rewrites_dead_word {α V T} (E : EDT0LGrammar α V T) (u v : List (Symbol α V))
  (h_u : E.IsDeadWord u) (h_rewrites : E.Rewrites u v) :
    E.IsDeadWord v := by
  obtain ⟨t, rfl⟩ := h_rewrites
  exact rewriteWord_dead_word E u h_u t

lemma derives_dead_word {α V T} (E : EDT0LGrammar α V T) (u v : List (Symbol α V))
  (h_u : E.IsDeadWord u) (h_derives : E.Derives u v) :
    E.IsDeadWord v := by
  induction h_derives with
  | refl =>
    exact h_u
  | tail x y h =>
    rename_i a b
    exact rewrites_dead_word E a b h y

end EDT0LGrammar
