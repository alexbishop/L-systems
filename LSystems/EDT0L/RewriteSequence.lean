/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs

/-!
# Sequences of rewrites

Suppsose that `E : EDT0LGrammar α V T`, and that `u v : List (Symbol α V)` are two words.  Then,
from the definitions provided in `LSystems.EDT0L.Defs`, we see that `E.Derives u v` if and only if
there exists some sequence of tables which can be used to rewrite `u` to `v`.  In this file, we give
an alternative definition which makes this sequence of tables explicit.

## Main definition

* `EDT0LGrammar.rewriteSeq E s w`: the word that would be obtained by applying the tables in `s` to
  the word `w` in order.  (see this definition for more details.)

## Main theorem

* `EDT0LGrammar.derives_iff_rewriteSeq`: shows that, in some way, `EDT0LGrammar.Derives` and
  `EDT0LGrammar.rewriteSeq` are equivalent.
-/

@[expose] public section

namespace EDT0LGrammar
variable {α V T} (E : EDT0LGrammar α V T)

/--
Suppose that $s = [s_1, s_2, ..., s_k]$ is a sequence of tables, and that $w$ is some word.  Then,
we may define a sequence of words $w_1, w_2, ..., w_k$ where $w_1$ is the word `E.rewriteWord s₁ w`,
and $w_{i+1}$ is the word `E.rewriteWord sᵢ wᵢ` for each $i \in \{ 1,2,...,k - 1 \}$.  We then
define `E.rewriteSeq s w` to be the word $w_k$, that is, the word obtained by applying the sequence
of tables $s$ to the word $w$.

This definition is important for the definition of the class of LULT EDT0L grammars as defined in
`LSystems.FiniteIndexEDT0L.LULT`.
-/
def rewriteSeq (s : List T) (w : List (Symbol α V)) : List (Symbol α V) :=
  List.foldl (fun w' τ ↦ E.rewriteWord τ w') w s

@[simp]
lemma rewriteSeq_refl (w : List (Symbol α V)) : E.rewriteSeq [] w = w := rfl

@[simp]
lemma rewriteSeq_nil (s : List T) : E.rewriteSeq s [] = [] := List.foldl_fixed' (congrFun rfl) s

@[simp]
lemma rewriteSeq_seq_single (t : T) (w : List (Symbol α V)) :
    E.rewriteSeq [t] w = E.rewriteWord t w := rfl

@[simp]
lemma rewriteSeq_seq_append_singleton {t : T} {ts : List T} {u : List (Symbol α V)} :
    E.rewriteSeq (ts ++ [t]) u = E.rewriteWord t (E.rewriteSeq ts u) := List.foldl_concat _ u t ts

@[simp]
lemma rewriteSeq_seq_cons {t : T} {ts : List T} {u : List (Symbol α V)} :
    E.rewriteSeq (t::ts) u = E.rewriteSeq ts (E.rewriteWord t u) := List.foldl_cons

@[simp]
lemma rewriteSeq_seq_append (t s w) :
    E.rewriteSeq (s ++ t) w = E.rewriteSeq t (E.rewriteSeq s w) := List.foldl_append

@[simp]
lemma rewriteSeq_append (s : List T) (u v : List (Symbol α V)) :
    E.rewriteSeq s (u ++ v) = E.rewriteSeq s u ++ E.rewriteSeq s v := by
  induction s using List.reverseRec with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

lemma rewriteSeq_cons (s : List T) (a : Symbol α V) (as : List (Symbol α V)) :
    E.rewriteSeq s (a::as) = E.rewriteSeq s [a] ++ E.rewriteSeq s as := by
  rw [← rewriteSeq_append]
  simp only [List.cons_append, List.nil_append]

@[simp]
lemma rewriteSeq_terminals {s : List T} {u : List α} :
    E.rewriteSeq s (u.map .terminal) = u.map .terminal := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

@[simp]
lemma rewriteSeq_terminal {s : List T} {u : α} :
    E.rewriteSeq s [.terminal u] = [.terminal u] := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

theorem derives_iff_rewriteSeq (w w' : List (Symbol α V)) :
    E.Derives w w' ↔ ∃ s : List T, E.rewriteSeq s w = w' := by
  constructor
  · intro h
    induction h with
    | refl =>
      use []
      rfl
    | tail x y z =>
      rename_i a b
      obtain ⟨s, rfl⟩ := z
      obtain ⟨t, rfl⟩ := y
      exact ⟨s ++ [t], E.rewriteSeq_seq_append_singleton⟩
  · intro h
    obtain ⟨s, rfl⟩ := h
    induction s using List.reverseRecOn with
    | nil =>
      simp only [rewriteSeq_refl]
      exact derives_refl
    | append_singleton xs x ih =>
      simp only [rewriteSeq_seq_append, rewriteSeq_seq_cons, rewriteSeq_refl]
      exact derives_tail' ih x

theorem generates_iff_rewriteSeq (w : List (Symbol α V)) :
    E.Generates w ↔ ∃ s : List T, E.rewriteSeq s E.initialWord = w := by
  constructor
  · intro h
    induction h with
    | refl =>
      use []
      rfl
    | tail x y ih =>
      rename_i a b
      obtain ⟨s, rfl⟩ := ih
      obtain ⟨t, rfl⟩ := y
      use s ++ [t]
      simp
  · intro h
    obtain ⟨s, rfl⟩ := h
    induction s using List.reverseRecOn with
    | nil =>
      simp only [rewriteSeq_refl]
      exact generates_initial E
    | append_singleton xs x ih =>
      simp only [rewriteSeq_seq_append, rewriteSeq_seq_cons, rewriteSeq_refl]
      exact generates_rewriteWord_tail ih x

lemma generates_rewriteSeq {s : List T} : E.Generates (E.rewriteSeq s E.initialWord) := by
  simp [generates_iff_rewriteSeq]

lemma derives_rewriteSeq {s : List T} {w : List (Symbol α V)} : E.Derives w (E.rewriteSeq s w) := by
  simp [derives_iff_rewriteSeq]

@[simp]
lemma equiv_rewriteSeq {α' V' T'}
  (equivα : α ≃ α') (equivV : V ≃ V') (equivT : T ≃ T')
  (t : List T)
  (u : List (Symbol α V)) :
    ((equiv equivα equivV equivT E).rewriteSeq (t.map equivT) (equivWord equivα equivV u)) =
      equivWord equivα equivV (E.rewriteSeq t u) := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

@[simp]
lemma equiv_rewriteSeq' {α' V' T'}
  (equivα : α ≃ α') (equivV : V ≃ V') (equivT : T ≃ T')
  (t : List T')
  (u : List (Symbol α' V')) :
    ((equiv equivα equivV equivT E).rewriteSeq t u) =
      equivWord equivα equivV (E.rewriteSeq (t.map equivT.symm)
        (equivWord equivα.symm equivV.symm u)) := by
  have := E.equiv_rewriteSeq equivα equivV equivT
    (t.map equivT.symm) (equivWord equivα.symm equivV.symm u)
  simpa

end EDT0LGrammar
