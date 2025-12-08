/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar

structure DFAData (α Q : Type*) [Fintype α] [Fintype Q] where
  M : DFA α Q

namespace DFAData
variable {α Q : Type*} [Fintype α] [Fintype Q]
variable (data : DFAData α Q)

noncomputable def grammar : EDT0LGrammar α Q (α ⊕ Unit) where
  initial := data.M.start
  tables := fun h ↦ match h with
    | .inl t =>
      fun (q : Q) ↦ [Symbol.terminal t, Symbol.nonterminal (data.M.step q t)]
    | .inr _ => fun (q : Q) =>
      have _prop_dec (q : Q) : Decidable (q ∈ data.M.accept) := Classical.propDecidable _
      if q ∈ data.M.accept then [] else [ .nonterminal q ]

lemma generated_words (w : List (Symbol α Q)) :
  data.grammar.generates w → ∃ u : List α,
    (u.map .terminal = w ∧ data.M.evalFrom data.M.start u ∈ data.M.accept)
    ∨ (w = (u.map .terminal) ++ [.nonterminal (data.M.evalFrom data.M.start u)]) := by 
  --
  intro h
  unfold EDT0LGrammar.generates at h
  unfold EDT0LGrammar.derives at h
  induction h
  case refl =>
    use []
    right
    simp_all only [List.map_nil, DFA.evalFrom_nil,
        List.nil_append, List.cons.injEq, Symbol.nonterminal.injEq,   and_true]
    rfl
  case tail x y ih₁ ih₂ ih₃ =>
    replace ⟨u, ih₃⟩ := ih₃ 
    cases ih₃
    case inl ih₃ =>
      replace ⟨ih₃, ih₄⟩ := ih₃
      subst ih₃
      replace ih₂ := EDT0LGrammar.rewrites_terminals data.grammar ih₂
      subst ih₂
      use u
      left
      constructor
      · rfl
      · exact ih₄ 
    case inr ih₃ => 
      unfold EDT0LGrammar.rewrites at ih₂
      unfold EDT0LGrammar.rewriteWord at ih₂
      unfold EDT0LGrammar.rewriteSymbol at ih₂
      replace ⟨τ, ih₂⟩ := ih₂
      cases τ
      case inl τ => 
        use u ++ [τ]
        right
        unfold DFAData.grammar at ih₂
        simp only [] at ih₂
        subst ih₂
        subst ih₃
        clear ih₁
        rw [List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
          List.map_cons, List.map_nil, DFA.evalFrom_append_singleton, List.append_assoc,
          List.cons_append, List.nil_append, List.append_cancel_right_eq]
        induction u
        case nil =>
          simp only [List.map_nil, List.flatMap_nil]
        case cons a as ih =>
          simp_all only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      case inr τ =>
        use u
        by_cases h : data.M.evalFrom data.M.start u ∈ data.M.accept
        · left
          constructor
          · rw [ih₃] at ih₂
            rw [List.flatMap_append] at ih₂
            conv at ih₂ =>
              arg 1
              arg 1
              unfold DFAData.grammar
              simp only
              rw [List.flatMap_map]
              simp only
            conv at ih₂ =>
              arg 1
              arg 2
              unfold DFAData.grammar
              simp only
              simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
              simp only [h]
              simp only [↓reduceIte]
            subst ih₂
            clear ih₁
            clear ih₃
            clear h
            simp only [List.append_nil]
            induction u
            · simp_all only [List.map_nil, List.flatMap_nil]
            · rename_i a as ih
              simp_all only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
          · exact h
        · right
          simp only [ih₃] at ih₂
          rw [List.flatMap_append] at ih₂
          conv at ih₂ =>
            arg 1
            arg 2
            unfold DFAData.grammar
            simp only
          subst ih₂
          subst ih₃
          clear ih₁
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, h]
          conv =>
            lhs
            rhs
            change [Symbol.nonterminal (data.M.evalFrom data.M.start u)]
          rw [List.flatMap_map]
          simp only [List.append_cancel_right_eq]
          clear h
          induction u
          · simp_all only [List.map_nil, List.flatMap_nil]
          · rename_i a as ih
            simp_all only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]

lemma generated_words' (w : List α) :
  data.grammar.generates (
    (w.map .terminal)
      ++ [.nonterminal (data.M.evalFrom data.M.start w)]) := by 
  --
  unfold EDT0LGrammar.generates
  unfold EDT0LGrammar.derives
  induction w using List.reverseRecOn with
  | nil =>
    simp_all only [List.map_nil, DFA.evalFrom_nil, List.nil_append]
    rfl
  | append_singleton as a h =>
    have h' :
      data.grammar.rewrites
        (List.map Symbol.terminal as
          ++ [Symbol.nonterminal (data.M.evalFrom data.M.start as)])
        (List.map Symbol.terminal (as ++ [a])
          ++ [Symbol.nonterminal (data.M.evalFrom data.M.start (as ++ [a]))]) := by
      --
      unfold EDT0LGrammar.rewrites
      use .inl a
      unfold EDT0LGrammar.rewriteWord
      unfold EDT0LGrammar.rewriteSymbol
      unfold DFAData.grammar
      simp only 
      rw [List.flatMap_append]
      rw [List.flatMap_map]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
        List.map_cons, List.map_nil, DFA.evalFrom_append_singleton, List.append_assoc,
        List.cons_append, List.nil_append, List.append_cancel_right_eq]
      clear h
      induction as with
      | nil => simp only [List.flatMap_nil, List.map_nil]
      | cons as_head as_tail h =>
        simp_all only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]

    exact Relation.ReflTransGen.tail h h'

theorem languages_are_identical (w : List α) :
    data.grammar.generates (w.map .terminal) ↔ data.M.evalFrom data.M.start w ∈ data.M.accept := by
  --
  constructor
  · intro h
    replace ⟨u, h⟩ := data.generated_words (w.map .terminal) h
    cases h
    · rename_i h
      have ⟨left, right⟩ := h
      replace left : u = w := by
        clear right
        clear h
        let f := fun (a : α) ↦ (.terminal a : Symbol α Q)
        have hh : Function.Injective f := by
          unfold Function.Injective
          intro a₁ a₂ a
          simp_all only [Symbol.terminal.injEq, f]
        replace hh := List.map_injective_iff.mpr hh
        unfold Function.Injective at hh
        exact hh left
      subst left
      simp_all only [true_and]
    · rename_i h
      exfalso
      have h' : List.getLast (w.map Symbol.terminal)
                (by
                  simp_all only [
                    ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff,
                    List.cons_ne_self, and_false, not_false_eq_true])
              = .nonterminal (data.M.evalFrom data.M.start u) := by
        --
        simp_all only [ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_append_of_ne_nil,
          List.getLast_singleton]
      --
      simp only [List.getLast_map] at h'
      simp_all only [reduceCtorEq]
  · intro h
    have h' := data.generated_words' w
    unfold EDT0LGrammar.generates
    unfold EDT0LGrammar.derives
    apply Relation.ReflTransGen.tail h' ?_
    unfold EDT0LGrammar.rewrites
    use .inr ()
    unfold EDT0LGrammar.rewriteWord
    unfold EDT0LGrammar.rewriteSymbol
    unfold DFAData.grammar
    simp only
    rw [List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [h]
    simp only [↓reduceIte, List.append_nil]
    rw [List.flatMap_map]
    clear h
    clear h'
    induction w
    · simp only [List.flatMap_nil, List.map_nil]
    · rename_i head tail ih
      simp_all only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]

end DFAData

theorem regular_languages_are_edt0l {α : Type*} [Fintype α] (L : Language α) :
    L.IsRegular → L.IsEDT0L := by
  --
  unfold Language.IsRegular
  intro h
  have ⟨ _, _, M, h₁ ⟩ := h
  --
  let data := DFAData.mk M
  have h₂ := data.languages_are_identical

  let E := data.grammar

  have h₃ : E.language = M.accepts := by
    unfold EDT0LGrammar.language
    unfold DFA.accepts
    unfold DFA.acceptsFrom
    subst h₁
    simp_all only [exists_const_iff, data, E]

  rw [h₁] at h₃
  rw [← h₃]
  exact edt0l_grammars_generate_edt0l_languages E

end EDT0LGrammar
