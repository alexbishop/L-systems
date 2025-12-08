/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar

section SymbolIsNonterminal
variable {α V : Type*} 

def SymbolIsNonterminal : Symbol α V → Bool
  | .terminal _ => false
  | .nonterminal _ => true

@[simp]
lemma SymbolIsNonterminal_nonterminal (v : V) :
    (@SymbolIsNonterminal α V) (.nonterminal v) = true := rfl

@[simp]
lemma SymbolIsNonterminal_terminal (a : α) :
    (@SymbolIsNonterminal α V) (.terminal a) = false := rfl

@[simp]
lemma SymbolIsNonterminal_single_nonterminal (v : V) :
    List.countP (@SymbolIsNonterminal α V) [.nonterminal v] = 1 := rfl

end SymbolIsNonterminal

variable {α V T : Type*} [Fintype V] [Fintype T]
variable (E : EDT0LGrammar α V T)

def IsIndex (k : ℕ) : Prop :=
  ∀ w : List (Symbol α V), E.generates w → w.countP SymbolIsNonterminal ≤ k

lemma generates_implies_le_index {k : ℕ} (w : List (Symbol α V)) (h : E.IsIndex k) :
    E.generates w → List.countP SymbolIsNonterminal w ≤ k := by
  intro h'
  unfold IsIndex at h
  replace h := h w h'
  exact h

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

def Language.IsFiniteIndexEDT0L {α : Type*} (L : Language α) : Prop :=
  ∃ k : ℕ, L.IsEDT0LOfIndex k

lemma edt0l_of_index_implies_finite_index {α : Type*} (L : Language α) (k : ℕ) :
    L.IsEDT0LOfIndex k → L.IsFiniteIndexEDT0L := fun h ↦ ⟨k, h⟩

namespace EDT0LGrammar
variable {α V T : Type*} [Fintype V] [Fintype T]
variable (E : EDT0LGrammar α V T)

namespace EquivData
variable {α V T V' T' : Type*} [Fintype V] [Fintype T] [Fintype V'] [Fintype T']
variable (data : @EquivData α V T V' T' _ _ _ _)

lemma equivSymbol_preserves_nonterminal (a : Symbol α V') :
    SymbolIsNonterminal a = SymbolIsNonterminal (data.equivSymbol.symm a) := by
  unfold SymbolIsNonterminal
  split <;> rfl

lemma equiv_preserves_fi {k : ℕ} (h : data.E.IsIndex k) :
    data.grammar.IsIndex k := by
  unfold EDT0LGrammar.IsIndex
  intro w h₁
  replace h := h (data.equivWord.symm w)
  have h' := (data.grammar_generates_iff (w := data.equivWord.symm w)).mpr
  simp only [Equiv.apply_symm_apply] at h'
  replace h := h (h' h₁)
  unfold EquivData.equivWord at h
  simp only [Equiv.coe_fn_symm_mk, List.countP_map] at h
  conv at h =>
    left; arg 1
    change fun a ↦ SymbolIsNonterminal (data.equivSymbol.symm a)
    intro a
    rw [← equivSymbol_preserves_nonterminal]
  exact h

end EquivData

theorem fi_edt0l_grammars_generate_fi_edt0l_languages' {α V T : Type*} [Fintype V] [Fintype T]
  {k : ℕ}
  (E : EDT0LGrammar α V T) (h : E.IsIndex k) :
    E.language.IsEDT0LOfIndex k := by
  rename_i finN finH
  have isoN := finN.equivFin
  have isoH := finH.equivFin
  let equiv_data := EquivData.mk E isoN isoH
  let E' := equiv_data.grammar
  use finN.card, finH.card, E'
  have h₁ : E'.IsIndex k := by exact EquivData.equiv_preserves_fi equiv_data h
  use h₁
  replace h₁ := equiv_data.equiv_eq_language
  exact Eq.symm h₁

theorem fi_edt0l_grammars_generate_fi_edt0l_languages {α V T : Type*} [Fintype V] [Fintype T]
  (E : EDT0LGrammar α V T) (h : E.IsFiniteIndex) :
    E.language.IsFiniteIndexEDT0L := by
  replace ⟨k, h⟩ := h
  exact ⟨k, fi_edt0l_grammars_generate_fi_edt0l_languages' E h⟩

end EDT0LGrammar
