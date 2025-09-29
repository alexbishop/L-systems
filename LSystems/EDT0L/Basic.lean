/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

theorem trivial_EDT0L_grammars {T N H : Type*} [Fintype H] [Fintype N] [IsEmpty H]
  (E : EDT0LGrammar T N H) :
    E.language = 0 := by
  unfold EDT0LGrammar.language
  have hh (w : List T) : ¬ E.Generates (List.map .terminal w) := by
    intro h
    unfold EDT0LGrammar.Generates at h
    unfold EDT0LGrammar.Derives at h
    rw [Relation.reflTransGen_iff_eq_or_transGen] at h
    cases h with
    | inl h =>
      simp_all only [List.map_eq_singleton_iff, reduceCtorEq, and_false, exists_false]
    | inr h =>
      cases h with
      | single h => 
        unfold EDT0LGrammar.Rewrites at h
        simp_all only [IsEmpty.exists_iff]
      | tail _ h =>
        unfold EDT0LGrammar.Rewrites at h
        simp_all only [IsEmpty.exists_iff]
  simp only [hh]
  simp only [Set.setOf_false]
  rfl

theorem empty_language_is_EDT0L {α : Type*} : Language.IsEDT0L (0 : Language α) := by
  let E : EDT0LGrammar α (Fin 1) (Fin 0) := ⟨ 
    0,
    fun _ ↦ fun _ ↦ []
  ⟩
  have h := trivial_EDT0L_grammars E
  rw [Language.IsEDT0L]
  use 1, 0, E

theorem language_1_is_EDT0L {α : Type*} : Language.IsEDT0L (1 : Language α) := by
  let E : EDT0LGrammar α (Fin 1) (Fin 1) := ⟨ 
    0,
    fun _ ↦ fun _ ↦ []
  ⟩
  simp only [Language.IsEDT0L, EDT0LGrammar.language]

  have h : E.Derives [.nonterminal E.initial] [] := by
    unfold EDT0LGrammar.Derives
    apply Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) _
    use 0
    subst E
    simp only [Fin.isValue, EDT0LGrammar.RewriteWord.cons, EDT0LGrammar.RewriteSymbol.nonterminal,
      EDT0LGrammar.RewriteWord.nil, List.append_nil]

  have h : ∀ w :
      List (Symbol α (Fin 1)), E.Generates w → w = [Symbol.nonterminal 0] ∨ w = [] := by
    intro w
    intro h₁
    rw [EDT0LGrammar.Generates, EDT0LGrammar.Derives] at h₁

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
            rw [EDT0LGrammar.Rewrites] at h₃
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
            rw [EDT0LGrammar.Rewrites] at h₃
            have h₄ : ∀ τ : (Fin 1), τ = 0 := by
              --aesop?
              intro τ
              simp_all only [Fin.isValue, E]
              obtain ⟨w_1, h⟩ := h₃
              subst h
              ext : 1
              simp_all only [Fin.isValue, Fin.val_eq_zero]
            simp only [EDT0LGrammar.RewriteWord.nil, List.nil_eq, exists_const] at h₃
            rw [← h₃]
  -------------------
  use 1, 1, E

  have h₁ (w : List α) :
      E.Generates (List.map Symbol.terminal w) ↔ w = [] := by
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
      rw [EDT0LGrammar.Generates,EDT0LGrammar.Derives]
      simp only [List.map_nil]
      rw [Relation.reflTransGen_iff_eq_or_transGen]
      right
      rw [Relation.transGen_iff]
      left
      rw [EDT0LGrammar.Rewrites]
      use 0
      unfold EDT0LGrammar.RewriteWord
      unfold EDT0LGrammar.RewriteSymbol
      subst w₁
      simp_all only [Fin.isValue, List.flatMap_cons, List.flatMap_nil, List.append_nil, E]
  exact Language.ext_iff.mpr h₁
  -------------------

-- lemma language_of_partitions : 
--     -- Here a partition is a list of the form
--     --    [x_1, x_2, ..., x_n]
--     -- where each x_i ≥ 1, and x_i ≤ x_{i+1} for each i
--     --
--     -- This let constructs such a list from a list of the form
--     --    [(x_1 - 1), (x_3 - x_2), (x_4 - x_3), ..., (x_n - x_{n-1})]
--     -- It should be clear that all partitions can be constructed in this way
--     let diff_to_partition (diffs : List ℕ) :=
--       (List.mapAccumr
--         (fun (next : ℕ) (rtotal : ℕ) ↦ (next + rtotal, next + rtotal))
--         diffs 1).snd;
--     -- this let encodes a partition as a word over Fin 2
--     let diff_to_word (s : List ℕ) : List (Fin 2) := 
--       List.flatMap
--         (fun (n : ℕ) ↦ 0 :: (List.replicate n 1))
--         (diff_to_partition s)
--     -- the language of all such words
--     let lang := { diff_to_word s | s : List ℕ } ;
--     -- we prove here that this language is EDT0L
--     Language.IsEDT0L lang := by
--   --
--   extract_lets diff_to_partition diff_to_word lang
--   -- TODO
--   sorry



