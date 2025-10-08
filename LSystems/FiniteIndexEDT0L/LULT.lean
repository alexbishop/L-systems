/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import LSystems.EDT0L.DeriveSequence

namespace EDT0LGrammar

def ContainedAtMostOnce {α : Type*} (a : α) (s : List α) : Prop :=
  a ∉ s ∨ ∃ s₁ s₂ : List α, a ∉ s₁ ∧ a ∉ s₂ ∧ s = s₁ ++ [a] ++ s₂

def IsLULT {T N H : Type*} [Fintype N] [Fintype H] (E : EDT0LGrammar T N H) : Prop :=
  ∀ w ∈ E.language, ∃ a : List H,
  ∃ _ : E.DeriveSequence a [.nonterminal E.initial] = w.map .terminal,
    ∀ n : N, ∀ a₁ a₂ : List H, a = a₁ ++ a₂ →
        let before_split := E.DeriveSequence a₁ [.nonterminal E.initial];
        let after_split := E.DeriveSequence a₂ [.nonterminal n];
        (ContainedAtMostOnce (.nonterminal n) before_split) ∨ (List.length after_split ≤ 1)

end EDT0LGrammar

def Language.IsLULT {α : Type*} (L : Language α) : Prop :=
  ∃ n m : ℕ, ∃ E : EDT0LGrammar α (Fin n) (Fin m), ∃ _ : E.IsLULT, E.language = L

