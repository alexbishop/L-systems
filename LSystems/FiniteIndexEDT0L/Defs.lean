import LSystems.EDT0L.Defs

namespace EDT0LGrammar
variable {T N H : Type*} [Fintype N] [Fintype H]
variable (E : EDT0LGrammar T N H)

def SymbolIsNonterminal {T N : Type*} : Symbol T N → Bool
  | .terminal _ => false
  | .nonterminal _ => true

def IsIndex (k : ℕ) : Prop :=
  ∀ w : List (Symbol T N), E.Generates w → w.countP SymbolIsNonterminal ≤ k

def IsFiniteIndex : Prop := ∃ k : ℕ, E.IsIndex k

lemma index_at_least_one {k : ℕ} (h : E.IsIndex k) : k ≥ 1 := by
  by_contra x
  simp only [ge_iff_le, not_le, Nat.lt_one_iff] at x
  replace h := h [.nonterminal E.initial] E.generates_initial
  simp only [List.countP_singleton] at h
  unfold SymbolIsNonterminal at h
  subst x
  simp only [↓reduceIte, nonpos_iff_eq_zero, one_ne_zero] at h

end EDT0LGrammar

def Language.IsEDT0LOfIndex {α : Type*} (L : Language α) (k : ℕ) : Prop :=
  ∃ n m : ℕ, ∃ E : EDT0LGrammar α (Fin n) (Fin m), ∃ _ : E.IsIndex k, E.language = L

def Language.IsFiEDT0L {α : Type*} (L : Language α) : Prop :=
  ∃ k : ℕ, L.IsEDT0LOfIndex k

namespace EDT0LGrammar
variable {T N H : Type*} [Fintype N] [Fintype H]
variable (E : EDT0LGrammar T N H)

namespace EquivData
variable {T N H N' H' : Type*} [Fintype N] [Fintype H] [Fintype N'] [Fintype H']
variable (𝓖 : @EquivData T N H N' H' _ _ _ _)

lemma equiv_symbol_preserves_nonterminal (a : Symbol T N') :
    SymbolIsNonterminal a = SymbolIsNonterminal (𝓖.equiv_symbol.symm a) := by
  unfold SymbolIsNonterminal
  split <;> rfl

lemma equiv_preserves_fi {k : ℕ} (h : 𝓖.E.IsIndex k) :
    𝓖.grammar.IsIndex k := by
  unfold EDT0LGrammar.IsIndex
  intro w h₁
  replace h := h (𝓖.equiv_word.symm w)
  have h' := (𝓖.grammar_generates_iff (𝓖.equiv_word.symm w)).mpr
  simp only [Equiv.apply_symm_apply] at h'
  replace h := h (h' h₁)
  unfold EquivData.equiv_word at h
  simp only [Equiv.coe_fn_symm_mk, List.countP_map] at h
  conv at h =>
    left; arg 1
    change fun a ↦ SymbolIsNonterminal (𝓖.equiv_symbol.symm a)
    intro a
    rw [← equiv_symbol_preserves_nonterminal]
  exact h

end EquivData

theorem fi_edt0l_grammars_generate_fi_edt0l_languages' {T N H : Type*} [Fintype N] [Fintype H]
  {k : ℕ}
  (E : EDT0LGrammar T N H) (h : E.IsIndex k) :
    E.language.IsEDT0LOfIndex k := by
  rename_i finN finH
  have isoN := finN.equivFin
  have isoH := finH.equivFin
  let equiv_data := EquivData.mk E isoN isoH
  let E' := equiv_data.grammar
  use finN.card, finH.card, E'
  have h₁ : E'.IsIndex k := by exact EquivData.equiv_preserves_fi equiv_data h
  use h₁
  replace h₁ := equiv_data.equiv_has_same_language
  exact Eq.symm h₁

theorem fi_edt0l_grammars_generate_fi_edt0l_languages {T N H : Type*} [Fintype N] [Fintype H]
  (E : EDT0LGrammar T N H) (h : E.IsFiniteIndex) :
    E.language.IsFiEDT0L := by
  replace ⟨k, h⟩ := h
  exact ⟨k, fi_edt0l_grammars_generate_fi_edt0l_languages' E h⟩

end EDT0LGrammar
