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

@[simp]
lemma containedAtMostOnce_iff_count_le_one {α : Type*} [DecidableEq α] (a : α) (s) :
    ContainedAtMostOnce a s ↔ s.count a ≤ 1 := by
  constructor
  · intro h
    obtain h | h := h
    · rw [Nat.le_one_iff_eq_zero_or_eq_one]
      left
      exact List.count_eq_zero.mpr h
    · rw [Nat.le_one_iff_eq_zero_or_eq_one]
      right
      obtain ⟨s₁, s₂, h₁, h₂, rfl⟩ := h
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
        List.count_cons_self]
      replace h₁ := List.count_eq_zero.mpr h₁
      replace h₂ := List.count_eq_zero.mpr h₂
      rw [h₁, h₂]
  · intro h
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at h
    obtain h | h := h
    · unfold ContainedAtMostOnce
      left
      exact List.count_eq_zero.mp h
    · unfold ContainedAtMostOnce
      right
      let idx? := s.finIdxOf? a
      cases h₁ : idx? with
      | none =>
        exfalso
        unfold idx? at h₁
        replace h : a ∈ s := by
          clear * - h
          by_contra contra
          replace contra := List.count_eq_zero.mpr contra
          rw [h] at contra
          simp only [one_ne_zero] at contra
        exact List.finIdxOf?_eq_none_iff.mp h₁ h
      | some i =>
        unfold idx? at h₁
        replace ⟨h₁, _⟩ := List.finIdxOf?_eq_some_iff.mp h₁
        have h₂ : s = s.take i ++ [s[i]] ++ s.drop (i + 1) := by
          simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
        --
        rw [h₁] at h₂
        rw [h₂] at h
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
          List.count_cons_self] at h
        simp only [← Nat.add_assoc, Nat.add_eq_right, Nat.add_eq_zero] at h
        --
        have ⟨h_l, h_r⟩ := h
        --
        use
          s.take i,
          s.drop (i + 1),
          List.count_eq_zero.mp h_l,
          List.count_eq_zero.mp h_r,
          h₂

def IsLULT {α V T : Type*} [Fintype V] [Fintype T] (E : EDT0LGrammar α V T) : Prop :=
  ∀ w ∈ E.language,
  ∃ (a : List T) (_ : E.deriveSeq a [.nonterminal E.initial] = w.map .terminal),
    ∀ (i : ℕ) (_ : i ≤ a.length),
      let a₁ := a.take i;
      let a₂ := a.drop i;
      ∀ v : V,
        let before_split := E.deriveSeq a₁ [.nonterminal E.initial];
        let after_split := E.deriveSeq a₂ [.nonterminal v];
        (ContainedAtMostOnce (.nonterminal v) before_split) ∨ (after_split.length ≤ 1)

end EDT0LGrammar

def Language.IsLULT {α : Type*} (L : Language α) : Prop :=
  ∃ n m : ℕ, ∃ E : EDT0LGrammar α (Fin n) (Fin m), ∃ _ : E.IsLULT, E.language = L

namespace EDT0LGrammar
namespace EquivData
variable {α V T V' T' : Type*}
  [Fintype V] [Fintype T] [Fintype V'] [Fintype T']
  [DecidableEq α] [DecidableEq V] [DecidableEq V']
variable (data : @EquivData α V T V' T' _ _ _ _)

lemma equiv_preserves_lult (h : data.E.IsLULT) : data.grammar.IsLULT := by
  unfold IsLULT
  intro w w_in_lang
  replace ⟨a, a', h⟩ := h w (by rw [equiv_eq_language]; exact w_in_lang)
  use data.equivTableSeq a
  use (by
    rw [deriveSeq_equiv']
    simp only [Equiv.symm_apply_apply, equivWord_symm_cons, equiv_symbol_nonterminal',
      equivV_grammar_initial, equivWord_symm_nil]
    rw [a']
    simp only [equivWord_terminals])
  --
  simp only
  intro i hi v
  simp only [equivTableSeq_length] at hi
  --
  replace h := h i hi (data.equivV.symm v)
  simp only at h
  --
  obtain h | h := h
  · left
    simp only [containedAtMostOnce_iff_count_le_one] at h
    simp only [containedAtMostOnce_iff_count_le_one]
    change
      let x := _
      let s := _
      List.count x s ≤ 1
    extract_lets x s
    --
    have h₁ := List.count_map_of_injective
      s
      (data.equivSymbol.invFun)
      (by
        simp only [Equiv.invFun_as_coe]
        exact Equiv.injective data.equivSymbol.symm)
      x
    rw [← h₁]
    subst x s
    simp only [Equiv.invFun_as_coe, equiv_symbol_nonterminal']
    clear * - h
    --
    change List.count _ (data.equivWord.symm _) ≤ 1
    rw [deriveSeq_equiv] at h
    simp only [equivWord_cons, equiv_symbol_nonterminal, equivV_initial, equivWord_nil] at h
    --
    conv at h =>
      lhs
      arg 2
      arg 2
      arg 2
      change List.map _ _
      rw [List.map_take]
      change List.take _ (data.equivTableSeq a)
    exact h
  · right
    rw [deriveSeq_equiv] at h
    simp only [equivWord_cons, equiv_symbol_nonterminal, Equiv.apply_symm_apply, equivWord_nil] at h
    conv at h =>
      lhs
      arg 1
      arg 2
      arg 2
      change List.map _ _
      rw [List.map_drop]
      change List.drop _ (data.equivTableSeq _)
    change (List.map _ _).length ≤ 1 at h
    rw [List.length_map] at h
    exact h

end EquivData

end EDT0LGrammar
