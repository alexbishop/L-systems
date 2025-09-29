/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs
import LSystems.EDT0L.DeriveSequence

namespace EDT0LGrammar
variable {T N H : Type*} [Fintype N] [Fintype H]
variable (E : EDT0LGrammar T N H)
variable [BEq (Symbol T N)]

def IsLULT :=
  ∀ w ∈ E.language, ∃ a : List H,
  ∃ _ : E.DeriveSequence a [.nonterminal E.initial] = w.map .terminal,
    ∀ n : N, ∀ a₁ a₂ : List H, ∃ _ : a = a₁ ++ a₂,
      (List.count
        (.nonterminal n)
        (E.DeriveSequence a₁ [.nonterminal E.initial]) ≤ 1) ∨ 
      (List.length
        (E.DeriveSequence a₂ [.nonterminal n]) ≤ 1)

end EDT0LGrammar
