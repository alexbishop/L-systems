/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import LSystems.EDT0L.Basic

/-!
# Finite Index EDT0L Grammars

An EDT0L grammar is said to be index `k : ℕ`, if every derivation of the language contains at most
`k` nonterminals.  An EDT0L grammar is said to be fintie index if there exists such a `k`.

## Main definitions

* `EDT0LGrammar.IsIndex` A predicate indicating that a given EDT0L grammar as a given index
* `EDT0LGrammar.IsFiniteIndex` A predicate indicates that an EDT0L grammar has some index

**Language predicates:**

* `Language.IsEDT0LOfIndex L k`
  There is an EDT0L grammar of index k which generates the language `L`
* `Language.IsFiniteIndexEDT0L L`
  There is a finite index EDT0L grammar which generates the language `L`

## Main theorems

* `EDT0LGrammar.isIndex_imp_language_isEDT0LOfIndex`
  If an EDT0L grammar has index k, then its corresponding language has index k
* `EDT0LGrammar.isFiniteIndex_imp_language_isFiniteIndexEDT0L`
  If an EDT0L grammar is finite index, then its corresponding language is finite index
-/


@[expose] public section

namespace EDT0LGrammar

variable {α V T : Type*} (E : EDT0LGrammar α V T)

def IsIndex (k : ℕ) : Prop := ∀ w, E.Generates w → (filterNonterminals w).length ≤ k

def IsFiniteIndex : Prop := ∃ k : ℕ, E.IsIndex k

lemma isIndex_k_geq_one {k : ℕ} (h : E.IsIndex k) : k ≥ 1 := by
  by_contra contra
  simp only [ge_iff_le, not_le, Nat.lt_one_iff] at contra
  subst contra
  obtain h' := h _ E.generates_initial
  simp at h'

end EDT0LGrammar

def Language.IsEDT0LOfIndex {α : Type*} (L : Language α) (k : ℕ) : Prop :=
  ∃ n m : ℕ, ∃ E : EDT0LGrammar α (Fin n) (Fin m), E.IsIndex k ∧ E.language = L

def Language.IsFiniteIndexEDT0L {α : Type*} (L : Language α) : Prop :=
  ∃ k : ℕ, L.IsEDT0LOfIndex k

lemma Language.isEDT0LOfIndex_imp_isFiniteIndexEDT0L {α : Type*} (L : Language α) (k : ℕ) :
    L.IsEDT0LOfIndex k → L.IsFiniteIndexEDT0L := fun h ↦ ⟨k, h⟩

namespace EDT0LGrammar
variable {α V T : Type*} (E : EDT0LGrammar α V T)

private lemma equiv_isIndex {α' V' T'} (equivα : α ≃ α') (equivV : V ≃ V') (equivT : T ≃ T')
  (k : ℕ) (h : E.IsIndex k) :
    (E.equiv equivα equivV equivT).IsIndex k := by
  have k_geq_1 := isIndex_k_geq_one _ h
  intro w h'
  replace h := h _ ((equiv_generates equivα equivV equivT E w).mp h')
  clear * - h k_geq_1
  induction w generalizing k with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [filterNonterminals_cons, ge_iff_le]
    split
    · exact ih k k_geq_1 h
    · simp only [List.length_cons]
      rw [equivWord_symm, equivWord_cons] at h
      simp only [equivSymbol_nonterminal, ← equivWord_symm, filterNonterminals_cons,
        List.length_cons] at h
      cases h' : k - 1 with
      | zero =>
        have h'' : (filterNonterminals ((equivWord equivα equivV).symm xs)).length = 0 := by omega
        simp only [List.length_eq_zero_iff] at h''
        by_contra contra
        simp only [ge_iff_le, not_le] at contra
        simp only [filterNonterminals_equivWord_symm, List.map_eq_nil_iff] at h''
        rw [h''] at contra
        simp only [List.length_nil, zero_add, Nat.lt_one_iff] at contra
        omega
      | succ k' =>
        simp_all

@[simp← ]
lemma equiv_isIndex_iff {α' V' T'} (equivα : α ≃ α') (equivV : V ≃ V') (equivT : T ≃ T')
  (k : ℕ) :
    E.IsIndex k ↔ (E.equiv equivα equivV equivT).IsIndex k := by
  constructor
  · exact equiv_isIndex E equivα equivV equivT k
  · let E' := (equiv equivα equivV equivT) E
    have h' : E = (equiv equivα.symm equivV.symm equivT.symm) E' :=
      (Equiv.symm_apply_eq (equiv equivα.symm equivV.symm equivT.symm)).mp rfl
    conv => intro x ; rw [h']
    change E'.IsIndex k → _
    exact equiv_isIndex E' equivα.symm equivV.symm equivT.symm k

theorem isIndex_imp_language_isEDT0LOfIndex [Finite V] [Finite T] (k : ℕ) :
    E.IsIndex k → E.language.IsEDT0LOfIndex k := by
  intro h
  have := Fintype.ofFinite V
  have := Fintype.ofFinite T
  have h' := equiv_language_eq_language (Fintype.equivFin V) (Fintype.equivFin T) E
  unfold Language.IsEDT0LOfIndex
  exact ⟨_, _, _, (equiv_isIndex_iff E (Equiv.refl α) _ _ k).mp h, h'⟩

theorem isFiniteIndex_imp_language_isFiniteIndexEDT0L [Finite V] [Finite T] :
    E.IsFiniteIndex → E.language.IsFiniteIndexEDT0L := by
  intro h
  replace ⟨k, h⟩ := h
  replace h := isIndex_imp_language_isEDT0LOfIndex E k h
  exact Language.isEDT0LOfIndex_imp_isFiniteIndexEDT0L E.language k h

end EDT0LGrammar
