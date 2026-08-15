/-
Copyright (c) 2026 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Attach
public import LSystems.FiniteIndexEDT0L.LULT.Defs

@[expose] public section

namespace EDT0LGrammar

lemma attach_isLULT {α V T} [BEq V] (E : EDT0LGrammar α V T) (h : E.IsLULT) : E.attach.IsLULT := by
  intro w hw
  obtain ⟨s, h1, h2⟩ := h w.unattach (by 
    rw [← language_eq_attach_language_map_val]
    use w, hw
    simp)
  use s
  constructor
  · rw [attach_rewriteSeq (h := Eq.symm (unattachSymbolWord_initialWord (E := E)))] at h1
    refine unattachSymbolWord_congr ?_
    rw [h1]
    simp
  · intro v i hi
    replace h2 := h2 v i hi
    obtain h2 | h2 := h2
    · left
      rw [attach_rewriteSeq (h := Eq.symm (unattachSymbolWord_initialWord (E := E)))] at h2
      simp only [filterNonterminals_unattachSymbolWord] at h2
      exact h2
    · right
      rw [attach_rewriteSeq (w := [.nonterminal v]) (w' := [.nonterminal v]) (h := rfl)] at h2
      unfold unattachSymbolWord at h2
      simpa using h2

lemma attach_isLULT_iff {α V T} [BEq V] (E : EDT0LGrammar α V T) : E.attach.IsLULT ↔ E.IsLULT := by
  classical
  constructor
  · intro h w hw
    rw [← language_eq_attach_language_map_val] at hw
    obtain ⟨w', hw', h'⟩ := hw
    replace ⟨s, h1, h2⟩ := h w' hw'
    use s
    constructor
    · clear * - h1 h'
      subst h'
      simp only [forall_exists_index, List.map_subtype, List.map_id_fun', id_eq]
      rw [attach_rewriteSeq (h := Eq.symm (unattachSymbolWord_initialWord (E := E)))]
      rw [h1]
      simp
    · intro v i hi
      obtain h2 | h2 := h2 v i hi
      · left
        rw [attach_rewriteSeq (h := Eq.symm (unattachSymbolWord_initialWord (E := E)))]
        simp_all
      · right
        rw [attach_rewriteSeq (w := [.nonterminal v]) (w' := [.nonterminal v]) (h := rfl)]
        simp_all
  · exact attach_isLULT E

end EDT0LGrammar
