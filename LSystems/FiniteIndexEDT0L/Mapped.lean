/-
Copyright (c) 2026 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Mapped
public import LSystems.FiniteIndexEDT0L.Defs

@[expose] public section

namespace EDT0LGrammar

lemma map_isIndex {α V T α'} (f : α → α') (E : EDT0LGrammar α V T) {k} (h : E.IsIndex k) :
    (E.Mapped f).IsIndex k := by
  intro w hw
  rw [generates_iff_rewriteSeq] at hw
  obtain ⟨s, rfl⟩ := hw
  replace h := h (E.rewriteSeq s E.initialWord) E.generates_rewriteSeq
  simp only [mapped_initialWord, mapWord_cons, mapWord_nil, ge_iff_le]
  have h' := mapped_rewriteSeq f E s [.nonterminal E.initial]
  conv at h' =>
    lhs
    unfold mapWord
    rw [List.map_singleton]
    simp only
  rw [h']
  simpa using h

end EDT0LGrammar

lemma Language.map_isEDT0LOfIndex {α α'} (f : α → α') (L : Language α)
  {k} (h : L.IsEDT0LOfIndex k) :
    (L.map f).IsEDT0LOfIndex k := by
  obtain ⟨n,m,E,h,rfl⟩ := h
  use n,m,E.Mapped f, EDT0LGrammar.map_isIndex f E h
  exact EDT0LGrammar.mapped_language f E

lemma Language.map_isFiniteIndexEDT0L {α α'} (f : α → α') (L : Language α)
  (h : L.IsFiniteIndexEDT0L) :
    (L.map f).IsFiniteIndexEDT0L := by
  obtain ⟨k,h⟩ := h
  use k
  exact map_isEDT0LOfIndex f L h

