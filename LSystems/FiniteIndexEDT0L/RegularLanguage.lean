/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import LSystems.EDT0L.RegularLanguage
public import LSystems.FiniteIndexEDT0L.Defs

import LSystems.EDT0L.RewriteSequence

@[expose] public section

namespace EDT0LGrammar

lemma regular_isEDT0LOfIndex_one {α σ} [DecidableEq σ] (dfa : DFA α σ) :
    (Regular dfa).IsIndex 1 := by
  intro w hw
  rw [regular_generates_iff] at hw
  cases hw with
  | processing u h | done u h h_accept =>
    subst h
    simp

end EDT0LGrammar

theorem Language.isReguar_imp_isEDT0LOfIndex_one {α : Type*} [Finite α] (L : Language α) :
    L.IsRegular → L.IsEDT0LOfIndex 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  intro h
  replace ⟨σ, finσ, dfa, h⟩ := h
  rw [← EDT0LGrammar.regular_eq_dfa dfa] at h
  rw [← h]
  unfold Language.IsEDT0LOfIndex
  apply EDT0LGrammar.isIndex_imp_language_isEDT0LOfIndex
  exact EDT0LGrammar.regular_isEDT0LOfIndex_one dfa

