/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import LSystems.EDT0L.Basic
public import LSystems.EDT0L.RewriteSequence

@[expose] public section

namespace EDT0LGrammar

def mapWord {α α' V} (f : α → α') : List (Symbol α V) → List (Symbol α' V) :=
  List.map fun | .terminal a => .terminal (f a) | .nonterminal v => .nonterminal v

@[simp]
lemma mapWord_nil {α α' V} (f : α → α') : mapWord (V := V) f [] = [] := rfl

@[simp]
lemma mapWord_cons {α α' V} (f : α → α') (x : Symbol α V) (xs : List (Symbol α V)) :
    mapWord f (x::xs) =
      (match x with | .terminal a => .terminal (f a) | .nonterminal v => .nonterminal v)
      :: mapWord f xs := rfl

@[simp]
lemma mapWord_append {α α' V} (f : α → α') (x y : List (Symbol α V)) :
    mapWord f (x ++ y) = mapWord f x ++ mapWord f y := List.map_append

lemma mapWord_terminals {α α' V} (f : α → α') (w : List α) :
    mapWord (V := V) f (w.map .terminal) = w.map (fun x ↦ .terminal (f x)) := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma mapWord_eq_terminals {α α' V} (f : α → α') (w : List α') (v : List (Symbol α V))
  (h : mapWord f v = List.map Symbol.terminal w) :
    ∃ (u : List α), v = u.map .terminal :=
  let rec go :
      (w : List α') →
      (v : List (Symbol α V)) →
      (h : mapWord f v = List.map Symbol.terminal w) →
      ∃ (u : List α), v = u.map .terminal
    | [], [], h => ⟨[], rfl⟩
    | a::as, b::bs, h => by
      simp only [mapWord_cons, List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨u', hu'⟩ := go as bs h2
      split at h1
      · rename_i a'
        simp only [Symbol.terminal.injEq] at h1
        use a'::u'
        simpa using hu'
      · trivial
    | _::_, [], h => by simp_all
    | [], _::_, h => by simp_all
  go w v h

@[simp]
lemma filterNonterminals_mapWord {α α' V} (f : α → α') (w : List (Symbol α V)) :
    filterNonterminals (mapWord f w) = filterNonterminals w := by
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [mapWord_cons, filterNonterminals_cons, ih]
    split <;> rename_i heq <;> split at heq <;> simp_all

def Mapped {α α' V T} (f : α → α') (E : EDT0LGrammar α V T) : EDT0LGrammar α' V T where
  initial := E.initial
  table := fun t v ↦ mapWord f (E.table t v)

@[simp]
lemma mapped_initialWord {α α' V T} (f : α → α') (E : EDT0LGrammar α V T) :
    (Mapped f E).initialWord = mapWord f E.initialWord := rfl

@[simp]
lemma mapped_rewriteWord {α α' V T} (f : α → α') (E : EDT0LGrammar α V T) (t : T) (w) :
    (E.Mapped f).rewriteWord t (mapWord f w) = mapWord f (E.rewriteWord t w) := by
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [mapWord_cons, rewriteWord_cons, ih, mapWord_append, List.append_cancel_right_eq]
    split <;> rfl

@[simp]
lemma mapped_rewriteSeq {α α' V T} (f : α → α') (E : EDT0LGrammar α V T) (s : List T) (w) :
    (E.Mapped f).rewriteSeq s (mapWord f w) = mapWord f (E.rewriteSeq s w) := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

lemma mapped_language {α α' V T} (f : α → α') (E : EDT0LGrammar α V T) :
    (E.Mapped f).language = E.language.map f := by
  ext1 w
  simp only [language_mem_iff, generates_iff_rewriteSeq, mapped_initialWord, mapped_rewriteSeq]
  constructor
  · intro h
    obtain ⟨s, h⟩ := h
    obtain ⟨u, h'⟩ := mapWord_eq_terminals _ _ _ h
    use u
    constructor
    · simp only [language, Set.mem_setOf_eq, ← h']
      exact generates_rewriteSeq E
    · rw [h', mapWord_terminals] at h
      change List.map (Symbol.terminal ∘ f) _ = _ at h
      rw [← List.map_map (f := f) (g := (Symbol.terminal (T := α') (N := V))) (l := u)] at h
      simp only [List.map_terminal] at h
      exact h
  · intro h
    obtain ⟨w', h1, h2⟩ := h
    simp only [language, generates_iff_rewriteSeq, Set.mem_setOf_eq] at h1
    obtain ⟨s, h1⟩ := h1
    use s
    rw [h1]
    simp only [mapWord_terminals]
    change List.map (Symbol.terminal ∘ f) _ = _
    rw [← List.map_map (f := f) (g := (Symbol.terminal (T := α') (N := V))) (l := w')]
    simp only [List.map_terminal]
    exact h2

end EDT0LGrammar

lemma Language.isEDT0L_map {α α'} (f : α → α') (L : Language α) (h : L.IsEDT0L) :
    (L.map f).IsEDT0L := by
  obtain ⟨n, m, E, h⟩ := h
  use n, m, E.Mapped f
  subst h
  exact EDT0LGrammar.mapped_language f E

