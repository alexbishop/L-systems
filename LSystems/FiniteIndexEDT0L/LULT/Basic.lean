/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.FiniteIndexEDT0L.Defs
import LSystems.FiniteIndexEDT0L.LULT.Defs
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.Defs
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.Generates

namespace EDT0LGrammar

lemma lult_imp_fiedt0l {α} (L : Language α) :
    L.IsLULT → L.IsFiniteIndexEDT0L := by
  intro h
  obtain ⟨n,m,E,h,h'⟩ := h
  classical
  let E' := LULTImpFiEDT0L E
  have h₁ : E.language = E'.language := by
    unfold E' EDT0LGrammar.language
    simp only [LULTImpFiEDT0L.generates_iff, h]
  rw [h₁] at h'
  rw [← h']
  have h₂ := LULTImpFiEDT0L.finite_index E
  change E'.IsIndex _ at h₂
  simp only [Fintype.card_fin] at h₂
  use n + 1
  exact fi_edt0l_grammars_generate_fi_edt0l_languages' E' h₂

end EDT0LGrammar


