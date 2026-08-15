/-
Copyright (c) 2026 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Attach
public import LSystems.FiniteIndexEDT0L.Defs

@[expose] public section

namespace EDT0LGrammar

lemma attach_isIndex {α V T} [BEq V] (E : EDT0LGrammar α V T) {k : ℕ} (h : E.IsIndex k) :
    E.attach.IsIndex k := by
  intro w hw
  have := h (unattachSymbolWord w) (by
    simp_all only [generates_iff_rewriteSeq]
    obtain ⟨s, rfl⟩ := hw
    use s
    rw [attach_rewriteSeq (h := Eq.symm (unattachSymbolWord_initialWord (E := E)))] )
  simp_all

lemma attach_isIndex' {α V T} [BEq V] (E : EDT0LGrammar α V T) {k : ℕ} (h : E.attach.IsIndex k) :
    E.IsIndex k := by
  intro w hw
  rw [generates_iff_rewriteSeq] at hw
  obtain ⟨s, hw⟩ := hw
  rw [attach_rewriteSeq (h := Eq.symm unattachSymbolWord_initialWord)] at hw
  change let w' := _ ;  unattachSymbolWord  w' = _ at hw
  extract_lets w' at hw
  subst hw
  have := h w' (by
    subst w'
    exact generates_rewriteSeq E.attach )
  simp_all

lemma attach_isIndex_iff {α V T} [BEq V] (E : EDT0LGrammar α V T) {k : ℕ} :
    E.attach.IsIndex k ↔ E.IsIndex k := ⟨attach_isIndex' E, attach_isIndex E⟩

lemma attach_isFiniteIndex_iff {α V T} [BEq V] (E : EDT0LGrammar α V T) :
    E.attach.IsFiniteIndex ↔ E.IsFiniteIndex := by
  constructor
  · intro h
    obtain ⟨k, h⟩ := h
    rw [attach_isIndex_iff] at h
    exact ⟨_, h⟩
  · intro h
    obtain ⟨k, h⟩ := h
    rw [<- attach_isIndex_iff] at h
    exact ⟨_, h⟩

end EDT0LGrammar

