/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import Mathlib.Computability.DFA
public import LSystems.EDT0L.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Regular languages are EDT0L

In this file, we show that if a language `L : Language α` is regular, then it is also EDT0L.  We
note here that the definition of regular languages provided by Mathlib does not require the alphabet
`α` to be finite.  The main theorem in this file takes `Finite α` as a hypothesis as otherwise the
result would not follow.

## Main definition

* `EDT0LGrammar.Regular dfa`: an EDT0L grammar which produces the same gramar as the deterministic
  finite-state automaton `dfa`

## Main theorems

* `EDT0LGrammar.regular_eq_dfa`: the EDT0L grammar given by the definition above generates exactly
  the same language as the given dfa.
* `Language.isRegular_imp_isEDT0L`: with the additional hypothesis `Finite α`, a language is EDT0L
  if it is regular.
-/

@[expose] public section

namespace EDT0LGrammar

inductive Regular.encoded_table {α σ} (dfa : DFA α σ) where
  | step (a : α)
  | final (q : σ) (h : q ∈ dfa.accept)
deriving DecidableEq

instance {α σ} [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ]
  (dfa : DFA α σ) [DecidablePred (· ∈ dfa.accept)] :
    Fintype (Regular.encoded_table dfa) where
  elems :=
    (Fintype.elems.sup fun (a : α) ↦ { .step a }) ∪
    (Fintype.elems.sup fun (q : σ) ↦ (if h : q ∈ dfa.accept then { .final q h } else ∅))
  complete := by
    intro x
    cases x with
    | step a =>
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_sup]
      use a, Fintype.complete a
      rw [Finset.mem_singleton]
    | final q h =>
      refine Finset.mem_union_right _ ?_
      rw [Finset.mem_sup]
      use q, Fintype.complete q
      simp only [↓reduceDIte, Finset.mem_singleton, h]

def Regular {α σ} [DecidableEq σ] (dfa : DFA α σ) :
    EDT0LGrammar α σ (Regular.encoded_table dfa) where
  initial := dfa.start
  table :=
    fun
    | .step a, q => [.terminal a, .nonterminal (dfa.step q a)]
    | .final q' _, q => if q = q' then [] else [.nonterminal q]

inductive Regular.NormalForm {α σ} (dfa : DFA α σ) (w : List (Symbol α σ)) : Prop where
  | processing
      (u : List α)
      (h : w = u.map .terminal ++ [.nonterminal (dfa.evalFrom dfa.start u)])
  | done
      (u : List α)
      (h : w = u.map .terminal)
      (h_accept : dfa.evalFrom dfa.start u ∈ dfa.accept)

private lemma regular_generates_imp {α σ} [DecidableEq σ] (dfa : DFA α σ) (w : List (Symbol α σ)) :
    (Regular dfa).Generates w → Regular.NormalForm dfa w := by
  intro h
  induction h with
  | refl =>
    refine Regular.NormalForm.processing [] ?_
    simp only [List.map_nil, DFA.evalFrom_nil, List.nil_append]
    rfl
  | tail x y ih =>
    rename_i b c
    cases ih with
    | processing u h =>
      change (Regular dfa).Derives _ _ at x
      subst h
      obtain ⟨t, rfl⟩ := y
      simp only [rewriteWord_append, rewriteWord_terminals, rewriteWord_cons,
        rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil]
      unfold Regular
      simp only
      split
      · rename_i a
        refine Regular.NormalForm.processing (u ++ [a]) ?_
        simp only [List.map_append, List.map_cons, List.map_nil, DFA.evalFrom_append_singleton,
          List.append_assoc, List.cons_append, List.nil_append]
      · rename_i t q' h_accept
        split
        · rename_i h_accept'
          simp only [List.append_nil]
          subst h_accept'
          exact .done u rfl h_accept
        · exact Regular.NormalForm.processing u rfl
    | done u h h_accept =>
      subst h
      obtain ⟨t, rfl⟩ := y
      simp only [rewriteWord_terminals]
      exact Regular.NormalForm.done u rfl h_accept

private lemma regular_generated_processing_imp_generates {α σ} [DecidableEq σ]
  (dfa : DFA α σ) (w : List (Symbol α σ))
  (u : List α) (h : w = u.map .terminal ++ [.nonterminal (dfa.evalFrom dfa.start u)]) :
    (Regular dfa).Generates w := by
  subst h
  induction u using List.reverseRecOn with
  | nil =>
    simp only [List.map_nil, DFA.evalFrom_nil, List.nil_append]
    exact (Regular dfa).generates_initial
  | append_singleton as a ih =>
    apply generates_rewrites_tail ih ?_
    use .step a
    simp only [rewriteWord_append, rewriteWord_terminals, rewriteWord_cons,
      rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil, List.map_append,
      List.map_cons, List.map_nil, DFA.evalFrom_append_singleton, List.append_assoc,
      List.cons_append, List.nil_append, List.append_cancel_left_eq]
    rfl

lemma regular_generates_iff {α σ} [DecidableEq σ] (dfa : DFA α σ) (w : List (Symbol α σ)) :
    (Regular dfa).Generates w ↔ Regular.NormalForm dfa w := by
  constructor
  · exact regular_generates_imp dfa w
  · intro h
    cases h with
    | processing u h' =>
      exact regular_generated_processing_imp_generates dfa w u h'
    | done u h h_accept' =>
      have pre := regular_generated_processing_imp_generates dfa
        (w ++ [.nonterminal <| dfa.evalFrom dfa.start u]) u
        (by 
          simp only [List.append_cancel_right_eq]
          exact h )
      apply generates_rewrites_tail pre ?_
      use .final (dfa.evalFrom dfa.start u) ((DFA.mem_acceptsFrom dfa).mp h_accept')
      subst h
      simp only [rewriteWord_append, rewriteWord_terminals, rewriteWord_cons,
        rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil, List.append_right_eq_self]
      unfold Regular
      simp

theorem regular_eq_dfa {α σ} [DecidableEq σ] (dfa : DFA α σ) :
    (Regular dfa).language = dfa.accepts := by
  ext1 w
  constructor
  · intro h
    simp only [language_mem_iff] at h
    replace h := (regular_generates_iff dfa _).mp h
    cases h with
    | processing u h =>
      replace h := congrArg (List.getLast? (α := Symbol α σ)) h
      simp only [List.getLast?_map, List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at h
    | done u h h_accept =>
      obtain rfl : u = w := by
        clear * - h
        induction w generalizing u with
        | nil =>
          simp only [List.map_nil, List.nil_eq, List.map_eq_nil_iff] at h
          exact h
        | cons a as ih =>
          replace h := Eq.symm h
          rw [List.map_cons, List.map_eq_cons_iff] at h
          obtain ⟨a',as',h1, h2, h3⟩ := h
          --
          replace ih := ih as' (Eq.symm h3)
          simp only [Symbol.terminal.injEq] at h2
          subst ih h2
          exact h1
      exact h_accept
  · intro h
    simp only [language_mem_iff]
    refine (regular_generates_iff dfa (List.map Symbol.terminal w)).mpr ?_
    exact .done w rfl h

end EDT0LGrammar

theorem Language.isRegular_imp_isEDT0L {α} [Finite α] (L : Language α) :
    L.IsRegular → L.IsEDT0L := by
  classical
  have : Fintype α := Fintype.ofFinite α
  intro h
  replace ⟨σ, finσ, dfa, h⟩ := h
  rw [← EDT0LGrammar.regular_eq_dfa dfa] at h
  rw [← h]
  exact EDT0LGrammar.language_isEDT0L _
