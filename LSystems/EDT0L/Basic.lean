/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar

@[simp]
theorem no_tables_imp_eq_0 {α V T : Type*} [Fintype V] [Fintype T] [IsEmpty T]
  (E : EDT0LGrammar α V T) :
    E.language = 0 := by
  unfold EDT0LGrammar.language
  have hh (w : List α) : ¬ E.generates (List.map .terminal w) := by
    intro h
    unfold EDT0LGrammar.generates at h
    unfold EDT0LGrammar.derives at h
    rw [Relation.reflTransGen_iff_eq_or_transGen] at h
    cases h with
    | inl h =>
      simp_all only [List.map_eq_singleton_iff, reduceCtorEq, and_false, exists_false]
    | inr h =>
      cases h with
      | single h => 
        unfold EDT0LGrammar.rewrites at h
        simp_all only [IsEmpty.exists_iff]
      | tail _ h =>
        unfold EDT0LGrammar.rewrites at h
        simp_all only [IsEmpty.exists_iff]
  simp only [hh]
  simp only [Set.setOf_false]
  rfl

theorem language_0_is_EDT0L {α : Type*} : Language.IsEDT0L (0 : Language α) := by
  let E : EDT0LGrammar α (Fin 1) (Fin 0) := ⟨ 
    0,
    fun _ ↦ fun _ ↦ []
  ⟩
  use 1, 0, E, E.no_tables_imp_eq_0

theorem language_1_is_EDT0L {α : Type*} : Language.IsEDT0L (1 : Language α) := by
  let E : EDT0LGrammar α (Fin 1) (Fin 1) := ⟨ 
    0,
    fun _ ↦ fun _ ↦ []
  ⟩
  simp only [Language.IsEDT0L, EDT0LGrammar.language]

  have h : E.derives [.nonterminal E.initial] [] := by
    unfold EDT0LGrammar.derives
    apply Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) _
    use 0
    subst E
    simp only [Fin.isValue, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
      List.append_nil]

  have h : ∀ w :
      List (Symbol α (Fin 1)), E.generates w → w = [Symbol.nonterminal 0] ∨ w = [] := by
    intro w
    intro h₁
    rw [EDT0LGrammar.generates, EDT0LGrammar.derives] at h₁

    induction h₁ with
    | refl =>
        left
        simp only [E]
    | tail h₂ h₃ h₄ =>
        right
        cases h₄ with
        | inl h₄ =>
            rw [h₄] at h₃
            clear h₄
            rw [EDT0LGrammar.rewrites] at h₃
            have h₄ : ∀ τ : (Fin 1), τ = 0 := by
              --aesop?
              intro τ
              simp_all only [Fin.isValue, E]
              obtain ⟨w_1, h⟩ := h₃
              subst h
              ext : 1
              simp_all only [Fin.isValue, Fin.val_eq_zero]
            simp only [h₄,exists_const] at h₃ 
            clear h₄
            -- rw [EDT0LGrammar.RewriteWord] at h₃
            --
            cases h₃ with | refl
            --
            -- show_term bound
            rfl
        | inr h₄ =>
            rw [h₄] at h₃
            clear h₄
            rw [EDT0LGrammar.rewrites] at h₃
            have h₄ : ∀ τ : (Fin 1), τ = 0 := by
              --aesop?
              intro τ
              simp_all only [Fin.isValue, E]
              obtain ⟨w_1, h⟩ := h₃
              subst h
              ext : 1
              simp_all only [Fin.isValue, Fin.val_eq_zero]
            simp only [EDT0LGrammar.rewriteWord_nil, List.nil_eq, exists_const] at h₃
            rw [← h₃]
  -------------------
  use 1, 1, E

  have h₁ (w : List α) :
      E.generates (List.map Symbol.terminal w) ↔ w = [] := by
    constructor
    case mp =>
      intro w₁

      have h₂ : _ := h (List.map Symbol.terminal w) w₁ 

      cases h₂ with
        | inl h₂ =>
            simp_all only [List.map_eq_singleton_iff, reduceCtorEq, and_false, exists_false]
        | inr h₂ =>
            exact List.map_eq_nil_iff.mp h₂
    case mpr =>
      intro w₁
      rw [w₁]
      rw [EDT0LGrammar.generates,EDT0LGrammar.derives]
      simp only [List.map_nil]
      rw [Relation.reflTransGen_iff_eq_or_transGen]
      right
      rw [Relation.transGen_iff]
      left
      rw [EDT0LGrammar.rewrites]
      use 0
      unfold EDT0LGrammar.rewriteWord
      unfold EDT0LGrammar.rewriteSymbol
      subst w₁
      simp_all only [Fin.isValue, List.flatMap_cons, List.flatMap_nil, List.append_nil, E]
  exact Language.ext_iff.mpr h₁
  -------------------

variable {α V T : Type*} [Fintype V] [Fintype T]
variable {E : EDT0LGrammar α V T}

@[simp]
lemma rewriteWord_nonterminal_mem [BEq (Symbol α V)] [LawfulBEq (Symbol α V)]
  {w : List (Symbol α V)} {v} {t : T} :
    .nonterminal v ∈ E.rewriteWord t w ↔
      ∃ (y : V) (_hy : .nonterminal y ∈ w), .nonterminal v ∈ E.tables t y := by
  constructor
  · intro h
    induction w with
    | nil =>
      simp only [rewriteWord_nil, List.not_mem_nil] at h
    | cons a as ih =>
      simp only [rewriteWord_cons, List.mem_append] at h
      obtain h | h := h
      · cases a
        · simp only [rewriteSymbol_terminal, List.mem_cons, reduceCtorEq, List.not_mem_nil,
            or_self] at h
        · rename_i y
          exact ⟨y, List.mem_cons_self, h⟩
      · replace ⟨y,hy,ih⟩ := ih h
        exact ⟨y, List.mem_cons_of_mem a hy, ih⟩
  · intro h
    obtain ⟨y, hy, h⟩ := h
    let idx? := w.finIdxOf? (.nonterminal y)
    cases h₁ : idx?
    · subst idx?
      exfalso
      exact List.finIdxOf?_eq_none_iff.mp h₁ hy
    · rename_i i
      subst idx?
      rw [List.finIdxOf?_eq_some_iff] at h₁
      obtain ⟨h₁, h₂⟩ := h₁
      have h₃ : w.take i ++ [w[i]] ++ w.drop (i + 1) = w := by
        simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
      rw [h₁] at h₃
      rw [← h₃]
      simp only [List.append_assoc, List.cons_append, List.nil_append, rewriteWord_append,
        rewriteWord_cons, rewriteSymbol_nonterminal, List.mem_append]
      right
      left
      exact h

lemma rewriteWord_mem (w : List (Symbol α V)) (x : Symbol α V) (t : T) :
    x ∈ E.rewriteWord t w ↔ ∃ y ∈ w, x ∈ E.rewriteSymbol t y := by
  constructor
  · intro h
    induction w with
    | nil =>
      simp_all only [rewriteWord_nil, List.not_mem_nil]
    | cons a as ih =>
      rename_i a'
      simp_all only [
        rewriteWord_cons, List.mem_append, List.mem_cons,
        exists_eq_or_imp]
      cases h with
      | inl h_1 => simp_all only [true_or]
      | inr h_2 => simp_all only [forall_const, or_true]
  · intro h
    obtain ⟨y, hy, h⟩ := h
    have ⟨n, hy'⟩ := List.mem_iff_get.mp hy
    change w[n] = y at hy'
    have h₁ : w.take n ++ [w[n]] ++ w.drop (n + 1) = w := by
      simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
    simp only [hy'] at h₁
    rw [← h₁]
    simp only [List.append_assoc, List.cons_append, List.nil_append, rewriteWord_append,
      rewriteWord_cons, List.mem_append]
    right; left
    exact h

end EDT0LGrammar

