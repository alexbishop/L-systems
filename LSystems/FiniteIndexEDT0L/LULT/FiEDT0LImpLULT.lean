/-
Copyright (c) 2026 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.FiniteIndexEDT0L.Defs
public import LSystems.FiniteIndexEDT0L.LULT.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi

import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

namespace EDT0LGrammar
namespace FiEDT0L2LULT

@[ext]
structure Word (V : Type*) (k : ℕ) where
  ℓ : Fin (k + 1)
  get : Fin ℓ → V
deriving DecidableEq

instance (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) :
    Fintype (Word V k) where
  elems :=
    Fintype.elems.sup fun (ℓ : Fin (k + 1)) ↦
    Fintype.elems.sup fun (word : Fin ℓ → V) ↦
    {⟨ℓ, word⟩}
  complete := by
    intro x
    simp only [Finset.sup_singleton_apply, Finset.mem_sup, Finset.mem_image]
    exact ⟨x.ℓ, Fintype.complete _, x.get, Fintype.complete _, rfl⟩

structure Nonterminal (V : Type*) (k : ℕ) where
  word : Word V k
  i : Fin word.ℓ
deriving DecidableEq

instance (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) :
    Fintype (Nonterminal V k) where
  elems :=
    Fintype.elems.sup fun (word : Word V k) ↦
    Fintype.elems.sup fun (i : Fin word.ℓ) ↦
    {⟨word, i⟩}
  complete := by
    intro x
    simp only [Finset.sup_singleton_apply, Finset.mem_sup, Finset.mem_image]
    exact ⟨x.word, Fintype.complete _, x.i, Fintype.complete _, rfl⟩

namespace Nonterminal

def unlabel {V k} (v : Nonterminal V k) := v.word.get v.i

end Nonterminal

-- -----------------------

namespace Word

def mk' {α V k}
  {w : List (Symbol α V)}
  (h : List.length (filterNonterminals w) ≤ k) :
    Word V k where
  ℓ := ⟨List.length (filterNonterminals w), Nat.lt_succ_of_le h⟩
  get := (filterNonterminals w).get

def toList {V k} (v : Word V k) := List.ofFn v.get

def toNumberedList {V k} (v : Word V k) : List (Nonterminal V k) :=
  List.ofFn fun i ↦ ⟨v, i⟩

@[simp]
lemma mk'_toList {α V k}
  {w : List (Symbol α V)}
  (h : List.length (filterNonterminals w) ≤ k) :
    (mk' h).toList = filterNonterminals w := List.ofFn_get (filterNonterminals w)

lemma toNumberedList_nodup {V k} (v : Word V k) : v.toNumberedList.Nodup := by
  unfold toNumberedList
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_ofFn]
  simp only [ne_eq, Nonterminal.mk.injEq, heq_eq_eq, true_and]
  exact fun ⦃i j⦄ a ↦ Fin.ne_of_lt a

lemma toList_length {V k} (v : Word V k) : v.toList.length = v.ℓ := by simp [toList]

def rewriteFilterNonterminals {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T) :
    List V := filterNonterminals (List.flatMap (E.table t) v.toList)

def rewriteFilterNonterminalsTake {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T)
  (i : ℕ) : List V := filterNonterminals (List.flatMap (E.table t) (v.toList.take i))

def rewriteFilterNonterminalsGet {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T)
  (i : Fin v.ℓ) : List V := filterNonterminals (E.table t (v.get i))

def rewriteLength {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T) : ℕ :=
  List.length <| v.rewriteFilterNonterminals E t

def CanRewrite {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T) : Prop :=
   v.rewriteLength E t < k + 1

variable {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T) in
instance : Decidable (v.CanRewrite E t) := by
  unfold CanRewrite
  exact inferInstance

lemma canRewrite_rewriteSeq {α V T} (E : EDT0LGrammar α V T) {k} (h : E.IsIndex k)
  (xs : List T) (x : T) :
    (Word.mk'
        (w := E.rewriteSeq xs E.initialWord)
        (h _ E.generates_rewriteSeq)).CanRewrite E x := by
  simp only [Word.CanRewrite, Word.rewriteLength,
    Word.rewriteFilterNonterminals, Word.mk'_toList]
  rw [← filterNonterminals_rewriteSymbols, ← rewriteSeq_seq_append_singleton]
  rw [← Nat.le_iff_lt_add_one]
  exact h _ E.generates_rewriteSeq

def rewrite {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T) (h : v.CanRewrite E t) :
    Word V k where
  ℓ := ⟨v.rewriteLength E t, h⟩
  get := (v.rewriteFilterNonterminals E t).get

def numberNonterminals {α V k} (target : Word V k) :
    (w : List (Symbol α V)) →
    (i : ℕ) → (j : ℕ) →
    (h : filterNonterminals w = (target.toList.drop i).take j) →
    (h' : (filterNonterminals w).length = j) →
    List (Symbol α (Nonterminal V k))
  | [],_,_,_,_ => []
  | .terminal x::xs, i, j, h, h' =>
    .terminal x :: target.numberNonterminals xs i j (by simpa using h) (by simpa using h')
  | .nonterminal x::xs, i, j, h, h' =>
    .nonterminal ⟨target, ⟨i, by
      by_contra contra
      rw [← toList_length] at contra
      simp only [not_lt] at contra
      simp [List.drop_of_length_le contra] at h⟩⟩ ::
    target.numberNonterminals xs (i + 1) (j - 1) (by
      simp only [filterNonterminals_cons] at h
      cases j with
      | zero =>
        simp at h
      | succ m =>
        rw [Nat.add_comm m 1, List.take_add, List.take_one] at h
        unfold List.head? at h
        split at h
        · rename_i heq
          rw [heq] at h
          simp at h
        · rename_i a as heq
          simp only [Option.toList_some, List.drop_drop, List.cons_append, List.nil_append,
            List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          simpa using h)
      (by cases j with | zero => simp at h' | succ j' => simpa using h' )

def rewriteNonterminal {α V T k} (v : Word V k) (E : EDT0LGrammar α V T) (t : T)
  (h : v.CanRewrite E t) (i : Fin v.ℓ) :
    List (Symbol α (Nonterminal V k)) :=
  (v.rewrite E t h).numberNonterminals
    (E.table t (v.get i))
    (List.length <| v.rewriteFilterNonterminalsTake E t i)
    (List.length <| v.rewriteFilterNonterminalsGet E t i)
    (by
      unfold rewriteFilterNonterminalsTake rewriteFilterNonterminalsGet
      conv => rhs; arg 2; arg 2; unfold Word.rewrite Word.toList
      simp only
      unfold Word.rewriteFilterNonterminals
      --
      change let s := _; _ = List.take _ (List.drop _ s)
      intro s
      have : s = filterNonterminals (List.flatMap (E.table t) v.toList) := List.ofFn_get _
      rw [this]
      clear this
      --
      conv => rhs; arg 2; arg 2; rw [← List.take_append_drop (↑i) v.toList]
      rw [List.flatMap_append, filterNonterminals_append]
      simp only [List.drop_left']
      have : List.drop (↑i) v.toList = v.toList.get ⟨i, by simp [toList_length]⟩ ::
          List.drop (↑i + 1) v.toList := Eq.symm List.cons_get_drop_succ
      rw [this]
      clear this
      --
      rw [List.flatMap_cons, filterNonterminals_append]
      conv => rhs; arg 2; lhs; unfold Word.toList
      simp )
    rfl

end Word

-- -----------------------

namespace Nonterminal

def letter {V k} (v : Nonterminal V k) : V := v.word.get v.i

def rewrite {α V T k} (v : Nonterminal V k) (E : EDT0LGrammar α V T) (t : T)
  (h : v.word.CanRewrite E t) :
    List (Symbol α (Nonterminal V k)) := v.word.rewriteNonterminal E t h v.i

end Nonterminal

-- -----------------------

def UnlabelWord {α V} {k : ℕ}
  (w : List (Symbol α (Nonterminal V k))) :
    List (Symbol α V) :=
  w.map
    (fun
      | .terminal a => .terminal a
      | .nonterminal v => .nonterminal v.letter)

@[simp]
lemma unlabelWord_append {α V} {k : ℕ}
  (u v : List (Symbol α (Nonterminal V k))) :
    UnlabelWord (u ++ v) = UnlabelWord u ++ UnlabelWord v := List.map_append

@[simp]
lemma unlabelWord_cons {α V} {k : ℕ}
  (a : Symbol α (Nonterminal V k)) (as : List (Symbol α (Nonterminal V k))) :
    UnlabelWord (a::as) =
    (match a with
      | .terminal a => .terminal a
      | .nonterminal v => .nonterminal v.letter)
    :: UnlabelWord as := List.map_cons

@[simp]
lemma unlabelWord_nil {α V} {k : ℕ} : UnlabelWord (α := α) (V := V) (k := k) [] = [] := rfl

@[simp]
lemma unlabelWord_length {α V k} (w : List (Symbol α (Nonterminal V k))) :
    (UnlabelWord w).length = w.length := by simp [UnlabelWord]

@[simp]
lemma unlabelWord_numberNonterminals {α V k} (target : Word V k)
  (w : List (Symbol α V))
  (i j : ℕ)
  (h : filterNonterminals w = (target.toList.drop i).take j)
  (h' : (filterNonterminals w).length = j) :
    UnlabelWord (target.numberNonterminals w i j h h') = w := by
  let rec go : 
      (w : List (Symbol α V)) →
      (i j : ℕ) →
      (h : filterNonterminals w = (target.toList.drop i).take j) →
      (h' : (filterNonterminals w).length = j) →
        UnlabelWord (target.numberNonterminals w i j h h') = w
    | [],_,_,_,_ => rfl
    | a::as,i,j,h',h'' => by
      cases a with
      | terminal a =>
        unfold Word.numberNonterminals
        simp only [unlabelWord_cons, List.cons.injEq, true_and]
        simp only [filterNonterminals_cons] at h'
        exact go as i j h' h''
      | nonterminal v =>
        unfold Word.numberNonterminals
        simp only [unlabelWord_cons, List.cons.injEq, Symbol.nonterminal.injEq]
        simp only [filterNonterminals_cons] at h'
        cases j with
        | zero =>
          simp at h'
        | succ j' =>
          rw [Nat.add_comm, List.take_add] at h'
          cases hl : List.drop i target.toList with
          | nil =>
            simp [hl] at h'
          | cons b bs =>
            simp only [hl, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
              List.cons_append, List.nil_append, List.cons.injEq] at h'
            obtain ⟨rfl, h'⟩ := h'
            constructor
            · unfold Nonterminal.letter
              simp only
              replace hl := congrArg List.head? hl
              simp only [Word.toList, List.head?_drop, List.getElem?_ofFn, List.head?_cons,
                Option.dite_none_right_eq_some, Option.some.injEq] at hl
              obtain ⟨h, hl⟩ := hl
              exact hl
            · replace hl := congrArg (List.drop 1) hl
              simp only [List.drop_drop, List.drop_succ_cons, List.drop_zero] at hl
              subst hl
              simp only [Nat.add_one_sub_one]
              exact go _ _ _ h' (by
                clear * - h''
                simp only [filterNonterminals_cons, List.length_cons,
                  Nat.add_right_cancel_iff] at h''
                omega )
  exact go _ _ _ _ _

@[simp]
lemma Word.numberNonterminals_eq_nil {α V k} (target : Word V k)
  (w : List (Symbol α V))
  (i : ℕ)
  (h : filterNonterminals w = (target.toList.drop i).take 0)
  (h' : (filterNonterminals w).length = 0) :
    filterNonterminals (target.numberNonterminals w i 0 h h') = [] := by
  rw [List.eq_nil_iff_length_eq_zero]
  induction w with
  | nil =>
    rfl
  | cons x xs ih =>
    simp only [List.take_zero, List.length_eq_zero_iff, Subsingleton.forall₂_iff] at ih ⊢
    replace ih := ih (by
      simp only [filterNonterminals_cons, List.length_eq_zero_iff] at h'
      split at h' <;> simp_all )
    unfold numberNonterminals
    cases x with
    | terminal a => simp_all
    | nonterminal v => simp at h'

@[simp]
lemma list_append_eq_list_take_append {α} {u v x y : List α} :
    u ++ v = x.take u.length ++ y.take v.length ↔ u = x.take u.length ∧ v = y.take v.length := by
  constructor
  · intro h
    if huv : u.length ≤ x.length ∧ v.length ≤ y.length then
      constructor
      · replace h := congrArg (List.take u.length) h
        simp only [List.take_left', List.length_take, huv, inf_of_le_left] at h
        exact h
      · replace h := congrArg (List.drop u.length) h
        simp only [List.drop_left', List.length_take, huv, inf_of_le_left] at h
        exact h
    else
      exfalso
      simp only [not_and_or, not_le] at huv
      obtain hu | hv := huv
      · replace h := congrArg List.length h
        simp [min_eq_right (show x.length ≤ u.length by omega)] at h
        omega
      · replace h := congrArg List.length h
        simp [min_eq_right (show y.length ≤ v.length by omega)] at h
        omega
  · intro h
    conv => lhs ; rw [h.left, h.right]

@[simp]
lemma Word.numberNonterminals_nil {α V k} (target : Word V k)
  (i j : ℕ)
  (h : filterNonterminals (α := α) (V := V) [] = (target.toList.drop i).take j)
  (h' : (filterNonterminals (α := α) (V := V) []).length = j) :
    target.numberNonterminals [] i j h h' = [] := rfl

@[simp]
lemma Word.numberNonterminals_append {α V k} (target : Word V k)
  (u v : List (Symbol α V))
  (i j : ℕ)
  (h : filterNonterminals (u ++ v) = (target.toList.drop i).take j)
  (h' : (filterNonterminals (u ++ v)).length = j) :
    target.numberNonterminals (u ++ v) i j h h' =
      target.numberNonterminals u i
        (filterNonterminals u).length
        (by
          simp only [filterNonterminals_append, List.length_append] at h'
          subst h'
          simp only [filterNonterminals_append] at h
          rw [List.take_add] at h
          simp only [List.drop_drop, list_append_eq_list_take_append] at h
          rw [h.left]
          simp)
        rfl ++
      target.numberNonterminals v (i + (filterNonterminals u).length)
        (filterNonterminals v).length
        (by
          simp only [filterNonterminals_append, List.length_append] at h'
          subst h'
          simp only [filterNonterminals_append] at h
          rw [List.take_add] at h
          simp only [List.drop_drop, list_append_eq_list_take_append] at h
          rw [h.right]
          simp)
        rfl := by
  induction u generalizing i j with
  | nil =>
    subst h'
    simp_all
  | cons x xs ih =>
    subst h'
    cases x with
    | terminal a =>
      conv =>
        lhs
        arg 2
        rw [List.cons_append (a := .terminal a) (as := xs) (bs := v)]
      rw [numberNonterminals]
      conv =>
        lhs
        rhs
        simp only [List.cons_append, filterNonterminals_cons]
      --
      replace ih := ih i (filterNonterminals (xs ++ v)).length (by simp_all) rfl
      rw [ih]
      rfl
    | nonterminal n =>
      conv =>
        lhs
        arg 2
        rw [List.cons_append (a := .nonterminal n) (as := xs) (bs := v)]
      rw [numberNonterminals]
      conv =>
        lhs
        rhs
        tactic => simp only [List.cons_append, filterNonterminals_cons,
          List.length_cons, Nat.add_one_sub_one]
      --
      replace ih := ih (i + 1) (filterNonterminals (xs ++ v)).length
        (by
          refine (List.cons_inj_right n).mp ?_
          rw [List.cons_append (a := .nonterminal n) (as := xs) (bs := v)] at h
          conv at h =>
            lhs
            simp only [filterNonterminals_cons]
          rw [h]
          have h' :
            (n :: filterNonterminals (xs ++ v))[0]? =
            (List.take (filterNonterminals (Symbol.nonterminal n :: (xs ++ v))).length
              (List.drop i target.toList))[0]? := by rw [h]
          simp only [filterNonterminals_append, List.length_cons, List.length_append,
            Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, filterNonterminals_cons,
            List.getElem?_take_of_lt, List.getElem?_drop, add_zero] at h'
          --
          simp only [filterNonterminals_cons, List.length_cons]
          rw [Nat.add_comm _ 1, List.take_add, ← List.singleton_append, List.drop_drop]
          rw [List.append_cancel_right_eq]
          clear * - h'
          rw [List.some_eq_getElem?_iff] at h'
          obtain ⟨h, rfl⟩ := h'
          rw [List.take_one_drop_eq_of_lt_length h]
          rfl )
        rfl
      rw [ih]
      conv => rhs ; rw [numberNonterminals]
      simp only [filterNonterminals_cons, List.length_cons, Nat.add_one_sub_one, List.cons_append,
        List.cons.injEq, List.append_cancel_left_eq, true_and]
      simp only [Nat.add_comm (filterNonterminals xs).length 1, Nat.add_assoc]

@[simp]
lemma Word.numberNonterminals_length {α V k} (target : Word V k)
  (u : List (Symbol α V))
  (i j : ℕ)
  (h : filterNonterminals u = (target.toList.drop i).take j)
  (h' : (filterNonterminals u).length = j) :
    (target.numberNonterminals u i j h h').length = u.length := by
  induction u using List.reverseRecOn generalizing j with
  | nil =>
    simp
  | append_singleton xs x ih =>
    simp only [numberNonterminals_append, filterNonterminals_cons, filterNonterminals_nil,
      List.length_append, ih, List.length_cons, List.length_nil, zero_add, Nat.add_left_cancel_iff]
    split <;> rfl

@[simp]
lemma Word.numberNonterminals_single {α V k} (target : Word V k)
  (s : Symbol α V)
  (i j : ℕ)
  (h : filterNonterminals [s] = (target.toList.drop i).take j)
  (h' : (filterNonterminals [s]).length = j) :
    target.numberNonterminals [s] i j h h' =
      match s with
      | .terminal a => [.terminal a]
      | .nonterminal n => [.nonterminal ⟨target, ⟨i, by
        by_contra contra
        simp only [not_lt] at contra
        have : target.toList.length ≤ i := by simp [toList, contra]
        simp [List.drop_of_length_le this] at h ⟩⟩]
     := by split <;> rfl

@[simp]
lemma Word.numberNonterminals_filterNonterminals_length {α V k} (target : Word V k)
  (u : List (Symbol α V))
  (i j : ℕ)
  (h : filterNonterminals u = (target.toList.drop i).take j)
  (h' : (filterNonterminals u).length = j) :
    (filterNonterminals <| target.numberNonterminals u i j h h').length =
      (filterNonterminals u).length := by
  induction u using List.reverseRecOn generalizing j with
  | nil =>
    simp
  | append_singleton xs x ih =>
    simp only [numberNonterminals_append, filterNonterminals_cons, filterNonterminals_nil,
      filterNonterminals_append, List.length_append]
    change
      let j' := _
      let h := _
      let h' := _
      (filterNonterminals <| target.numberNonterminals _ i j' h h').length + _ = _
    intro j' h h'
    --
    rw [ih j' h h']
    simp only [Nat.add_left_cancel_iff]
    split
    · simp
    · simp only [List.length_cons, List.length_nil, zero_add]
      rfl

@[simp]
lemma filterNonterminals_numberNonterminals_filterNonterminals {α V k} (w : List (Symbol α V))
  (ww : Word V k) (i j h h') :
    filterNonterminals
      (ww.numberNonterminals
        (List.map (Symbol.nonterminal (T := α)) (filterNonterminals w)) i j h h') =
    filterNonterminals
      (ww.numberNonterminals w i j (by simp_all) (by subst h'; simp)) := by
  induction w using List.reverseRecOn generalizing j with
  | nil =>
    rfl
  | append_singleton xs x ih =>
    simp only [filterNonterminals_append, filterNonterminals_cons, filterNonterminals_nil,
      List.map_append, Word.numberNonterminals_append, filterNonterminals_map_nonterminal, ih,
      Word.numberNonterminals_single, List.append_cancel_left_eq]
    split <;> rfl

protected def grammar.initial_ {α V T : Type*} (E : EDT0LGrammar α V T) (k : ℕ)
  (h_index : E.IsIndex k) :
    Nonterminal V k :=
  ⟨⟨1, fun _ ↦ E.initial⟩, ⟨0, by
    have := E.isIndex_k_geq_one h_index
    cases k <;> simp_all⟩⟩

def grammar {α V T : Type*} (E : EDT0LGrammar α V T) (k : ℕ) (h : E.IsIndex k) :
    EDT0LGrammar α (Nonterminal V k) T where
  initial := grammar.initial_ E k h
  table :=
    fun t v ↦
      if can_rewrite : Word.CanRewrite v.word E t then
        v.rewrite E t can_rewrite
      else
        [.nonterminal (grammar.initial_ E k h)]

lemma Word.numberNonterminals_ext {α V k} {ww1 ww2 : Word V k} {i1 i2 j1 j2 : ℕ}
  {w1 w2 : List (Symbol α V)}
  {h1 h2 h1' h2'}
  (hww : ww1 = ww2)
  (hw : w1 = w2)
  (hi : i1 = i2) :
    ww1.numberNonterminals w2 i1 j1 h1 h1' = ww2.numberNonterminals w2 i2 j2 h2 h2' := by
  subst hww hw hi j1 j2
  rfl

lemma Word.toNumberedList_length {V k} (w : Word V k) :
    w.toNumberedList.length = w.toList.length := by simp [toNumberedList, toList]

lemma Word.toNumberedList_eq {α V} {k} (w : Word V k) :
    w.toNumberedList =
    filterNonterminals
      (numberNonterminals (α := α) w (w.toList.map .nonterminal) 0 w.toList.length (by simp)
        (by simp)) := by
  let rec go :
      (i : ℕ) →
      (hi : i ≤ w.toList.length) →
      (h : _) → (h' : _) →
      w.toNumberedList.take i =
      filterNonterminals
        (numberNonterminals (α := α) w ((w.toList.take i).map .nonterminal) 0 i h h')
    | 0, hi, h, h' => by simp
    | j + 1, hi, h, h' => by
      have R := go j (Nat.le_of_succ_le hi) (by simp_all)
        (by
          simp_all only [List.map_take, filterNonterminals_take_nonterminal, List.drop_zero,
            List.length_take, inf_of_le_left, inf_eq_left]
          exact Nat.le_of_succ_le hi )
      simp only [List.take_add_one, R, List.map_take, List.map_append]
      simp only [numberNonterminals_append, filterNonterminals_take_nonterminal, List.length_take,
        min_eq_left (show j ≤ w.toList.length by exact Nat.le_of_succ_le hi), zero_add,
        filterNonterminals_map_nonterminal, filterNonterminals_append, List.append_cancel_left_eq]
      unfold toNumberedList
      simp only [List.getElem?_ofFn]
      --
      split
      · simp only [Option.toList_some]
        have : j < w.toList.length := Nat.lt_of_lt_of_eq hi rfl
        simp only [this, getElem?_pos, Option.toList_some, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil, zero_add]
        rfl
      · rename_i h''
        unfold toList at hi
        rw [List.length_ofFn] at hi
        clear * - h'' hi
        exfalso
        omega
  have R := go w.toList.length (Nat.le_refl _) (by simp) (by simp)
  conv at R => lhs; simp only [← toNumberedList_length, List.take_length]
  rw [R]
  simp

lemma grammar_eq_toNumberedList {α V T} (E : EDT0LGrammar α V T) {k} (h : E.IsIndex k)
  (t : List T) :
    filterNonterminals ((grammar E k h).rewriteSeq t (grammar E k h).initialWord) =
    (Word.mk'
        (w := E.rewriteSeq t E.initialWord)
        (h _ E.generates_rewriteSeq)).toNumberedList := by
  induction t using List.reverseRecOn with
  | nil =>
    rw [Word.toNumberedList_eq (α := α)]
    simp only [grammar, rewriteSeq_refl, filterNonterminals_cons, filterNonterminals_nil,
      Word.mk'_toList, List.map_cons, List.map_nil, List.length_cons, List.length_nil, zero_add,
      Word.numberNonterminals, List.cons.injEq, and_true]
    unfold grammar.initial_ Word.mk' initialWord
    simp only [Fin.coe_ofNat_eq_mod, Nonterminal.mk.injEq, Word.mk.injEq, filterNonterminals_cons,
      filterNonterminals_nil, List.length_cons, List.length_nil, zero_add]
    split_ands
    · exact Fin.one_eq_mk_of_lt _
    · change let i := _ ; let j := _ ; let f : Fin i → _ := _ ; let g : Fin j → _ := _ ; f ≍ g
      intro i j f g
      rw [show g = fun _ ↦ E.initial by unfold g ; ext x ; simp]
      have : i = j := by
        subst i j
        have := E.isIndex_k_geq_one h
        aesop
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
    · rw [heq_iff_exists_eq_cast]
      have := E.isIndex_k_geq_one h
      use (by
        simp_all only [ge_iff_le, filterNonterminals_cons, filterNonterminals_nil, List.length_cons,
          List.length_nil, zero_add]
        have : 1 % (k + 1) = 1 := by aesop
        rw [this])
      refine Fin.ext_iff.mpr ?_
      rw [Fin.cast_eq_cast']
      simp
  | append_singleton xs x ih =>
    rw [Word.toNumberedList_eq (α := α)]
    conv => lhs ; simp only [rewriteSeq_seq_append, rewriteSeq_seq_cons, rewriteSeq_refl]
    rw [filterNonterminals_rewriteWord, ih]
    simp only [Word.toNumberedList_eq (α := α)]
    simp only [Word.mk'_toList, rewriteSeq_seq_append, rewriteSeq_seq_cons, rewriteSeq_refl]
    change
      let ww := _
      let ww' := _
      let w := _
      let w' := _
      filterNonterminals (EDT0LGrammar.rewriteWord _ _ (List.map _ (filterNonterminals (
        Word.numberNonterminals ww (List.map _ w) _ _ _ _)))) =
      filterNonterminals (Word.numberNonterminals ww' (List.map _ w') _ _ _ _)
    intro ww ww' w w'
    --
    have go (l : ℕ) (hl : l ≤ w.length) (h1 h1' h2 h2') :
        filterNonterminals (α := α)
            ((grammar E k h).rewriteWord x
              (List.map Symbol.nonterminal
                (filterNonterminals (α := α)
                  (ww.numberNonterminals (List.map Symbol.nonterminal (w.take l)) 0 l h1 h1')))) =
          filterNonterminals (α := α)
            (ww'.numberNonterminals
              (List.map Symbol.nonterminal
                (w'.take
                  (List.length
                    <| filterNonterminals
                    <| E.rewriteWord x
                    <| List.map .nonterminal
                    <| w.take l)))
              0
              (List.length
                    <| filterNonterminals
                    <| E.rewriteWord x
                    <| List.map .nonterminal
                    <| w.take l)
              h2 h2') := by
      clear * - hl
      induction l with
      | zero => simp
      | succ m ih =>
        if hm : m < w.length then
          -- have hm' : m + 1 ≤ w.length := by omega
          have : w[m]?.toList = [w.get ⟨m, hm⟩] := by simp
          simp only [List.take_add_one, this, List.map_append, Word.numberNonterminals_append,
            filterNonterminals_append, rewriteWord_append]
          replace ih := ih (by omega) (by simp [ww, w])
            (by
              simp_all only [List.map_take, filterNonterminals_take_nonterminal, List.drop_zero,
                List.length_take, inf_eq_left, getElem?_pos, Option.toList_some,
                List.get_eq_getElem]
              omega)
            (by simp [w', ww'])
            (by 
              simp only [List.map_take, filterNonterminals_take_nonterminal, List.length_take,
                inf_eq_left, w, w']
              clear * -
              conv => rhs ; rw [filterNonterminals_rewriteWord]
              change
                let w := _
                (filterNonterminals (E.rewriteWord _ (List.take _ w))).length ≤
                  (filterNonterminals (E.rewriteWord _ w)).length
              intro w
              conv => rhs; rw [← List.take_append_drop m w]
              rw [rewriteWord_append]
              simp)
          simp only [List.map_take, filterNonterminals_take_nonterminal, List.length_take,
            min_eq_left (show m ≤ w.length by omega), List.get_eq_getElem, List.map_cons,
            List.map_nil, filterNonterminals_cons, filterNonterminals_nil, List.length_cons,
            List.length_nil, zero_add, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
            List.append_nil, List.length_append]
          simp only [List.map_take] at ih
          rw [ih]
          simp only [List.take_add, Word.numberNonterminals_append]
          simp only [filterNonterminals_take_nonterminal, List.length_take, zero_add,
            filterNonterminals_append]
          --
          have :
            (filterNonterminals (E.rewriteWord x
              (List.take m (List.map Symbol.nonterminal w)))).length ≤ w'.length := by
            clear * -
            subst w'
            conv => rhs ; rw [filterNonterminals_rewriteWord]
            change
              let w := _
              (filterNonterminals (E.rewriteWord _ (List.take _ w))).length ≤
                (filterNonterminals (E.rewriteWord _ w)).length
            intro w
            conv => rhs; rw [← List.take_append_drop m w]
            rw [rewriteWord_append]
            simp
          simp only [min_eq_left this, List.append_cancel_left_eq]
          clear * -
          --
          simp only [grammar, Nonterminal.rewrite, Word.rewriteNonterminal, Word.numberNonterminals,
            filterNonterminals_cons, filterNonterminals_nil, List.map_cons, List.map_nil,
            rewriteWord_cons, rewriteSymbol_nonterminal, Word.canRewrite_rewriteSeq, ↓reduceDIte,
            rewriteWord_nil, List.append_nil, ww]
          --
          have hh1 : w' = filterNonterminals (List.flatMap (E.table x) w) := by
            simp only [w', w]
            exact filterNonterminals_rewriteSymbols (E.rewriteSeq xs E.initialWord) E x
          have hh2 : w = w.take m ++ [w[m]] ++ w.drop (m + 1) := by simp
          have hh3 :
            List.take
              (filterNonterminals (E.table x w[m])).length
              (List.drop
                (filterNonterminals
                  (E.rewriteWord x
                    (List.take m (List.map Symbol.nonterminal w)))).length
                  (List.map (Symbol.nonterminal (T := α)) w')) =
              List.map .nonterminal (filterNonterminals (E.table x w[m])) := by
            rw [hh1]
            conv => lhs; arg 2; arg 2; rw [hh2]
            simp only [List.flatMap_append]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
              filterNonterminals_append, List.map_append]
            change
              let a := _
              let b := _
              let ii := _
              let jj := _
              (List.take ii <| List.drop jj <| a ++ (b ++ _)) = _
            intro a b ii jj
            --
            have : jj = a.length := by
              subst a jj
              simp only [List.length_map]
              apply congrArg List.length
              rw [← List.map_take, rewriteWord, List.flatMap_map]
              simp
            rw [this]
            simp only [List.drop_left']
            clear this
            --
            have : ii = b.length := by
              subst ii b
              simp
            rw [this]
            simp only [List.take_left']
            clear this
            --
            subst b
            rfl
          --
          simp only [hh3]
          simp only [filterNonterminals_map_nonterminal]
          --
          conv => lhs; arg 1; arg 2; arg 3; change w[m]
          simp only [filterNonterminals_numberNonterminals_filterNonterminals]
          --
          refine congrArg filterNonterminals ?_
          --
          change 
            let ww'2 := _
            Word.numberNonterminals ww'2 _ _ _ _ _ = _
          intro ww'2
          have : ww' = ww'2 := by
            subst ww' ww'2
            unfold Word.rewrite Word.mk'
            ext
            · simp only [Word.rewriteLength, Word.rewriteFilterNonterminals, Word.toList,
                List.ofFn_get]
              exact Nat.succ_inj.mp (congrArg Nat.succ (congrArg List.length hh1))
            · simp only [Word.rewriteLength, Word.rewriteFilterNonterminals, Word.toList]
              rw [List.ofFn_get, filterNonterminals_rewriteSymbols]
          simp only [this]
          refine Word.numberNonterminals_ext rfl rfl ?_
          simp only [Word.rewriteFilterNonterminalsTake, Word.toList, Word.mk', List.ofFn_get]
          refine congrArg List.length ?_
          subst w
          clear * -
          rw [filterNonterminals_rewriteWord]
          induction E.rewriteSeq xs E.initialWord generalizing m with
          | nil =>
            simp
          | cons y ys ih =>
            simp only [filterNonterminals_cons, filterNonterminals_take_nonterminal, List.map_take]
            split
            · simp [ih]
            · if hm : m > 0 then
                rw [List.map_cons]
                repeat rw [List.take_cons (i := m) (h := hm)]
                simp [ih]
              else
                simp_all
        else
          exfalso
          omega
    replace go := go w.length
      (by simp)
      (by simp [w, ww])
      (by simp [w])
      (by simp [w, w', ww'])
      (by
        simp only [List.take_length, List.map_take, filterNonterminals_take_nonterminal,
          List.length_take, inf_eq_left, w, w']
        rw [@Nat.le_iff_lt_or_eq]
        right
        apply congrArg List.length
        exact Eq.symm (filterNonterminals_rewriteWord (E.rewriteSeq xs E.initialWord) E x) )
    simp only [List.take_length] at go
    rw [go]
    have :
      (filterNonterminals (E.rewriteWord x (List.map Symbol.nonterminal w))).length =
        w'.length := by
      unfold w w'
      rw [filterNonterminals_rewriteWord]
      simp only [filterNonterminals_map_nonterminal]
      apply congrArg List.length
      exact Eq.symm (filterNonterminals_rewriteWord (E.rewriteSeq xs E.initialWord) E x)
    simp [this]
    rfl

lemma grammar_normalForm {α V T : Type*} (E : EDT0LGrammar α V T) (k : ℕ)
  (h : E.IsIndex k) (s : List T) :
    UnlabelWord ((grammar E k h).rewriteSeq s (grammar E k h).initialWord) =
    (E.rewriteSeq s E.initialWord) := by
  induction s using List.reverseRecOn with
  | nil =>
    rfl
  | append_singleton xs x ih =>
      simp only [rewriteSeq_seq_append, rewriteSeq_seq_cons, rewriteSeq_refl]
      have go (i : ℕ) :
          UnlabelWord
              ((grammar E k h).rewriteWord x
                (((grammar E k h).rewriteSeq xs (grammar E k h).initialWord).take i)) =
          E.rewriteWord x
              (UnlabelWord
                (((grammar E k h).rewriteSeq xs (grammar E k h).initialWord).take i)) := by
        induction i with
        | zero =>
          rfl
        | succ i ih =>
          rw [List.take_add_one]
          if hi : i < ((grammar E k h).rewriteSeq xs (grammar E k h).initialWord).length then
            simp only [getElem?_pos, Option.toList_some, rewriteWord_append, rewriteWord_cons,
              rewriteWord_nil, List.append_nil, unlabelWord_append, unlabelWord_cons,
              List.append_cancel_left_eq, ih, hi, unlabelWord_nil, rewriteWord_nil,
              List.append_nil]
            split <;> rename_i heq <;> rw [heq]
            · simp
            · rename_i v
              have hh : .nonterminal v ∈ (grammar E k h).rewriteSeq
                  xs (grammar E k h).initialWord := List.mem_of_getElem heq
              rw [← filterNonterminals_mem_iff, grammar_eq_toNumberedList, Word.toNumberedList]
                at hh
              simp only [List.mem_ofFn] at hh
              --
              have : v.word.CanRewrite E x := by
                obtain ⟨ii, rfl⟩ := hh
                unfold Word.CanRewrite Word.rewriteLength Word.rewriteFilterNonterminals
                simp only [Word.mk'_toList]
                --
                have (w : List V) :
                    List.flatMap (E.table x) w = E.rewriteWord x (w.map .nonterminal) := by
                  simp [rewriteWord, List.flatMap_map]
                simp only [this, gt_iff_lt]
                clear this
                --
                rw [← filterNonterminals_rewriteWord,
                  ← rewriteSeq_seq_single,
                  ← rewriteSeq_seq_append]
                --
                have := h (E.rewriteSeq (xs ++ [x]) E.initialWord) E.generates_rewriteSeq
                exact Nat.lt_succ_of_le this
              simp only [grammar, Nonterminal.rewrite, Word.rewriteNonterminal,
                rewriteSymbol_nonterminal, this, ↓reduceDIte]
              exact
                unlabelWord_numberNonterminals
                (v.word.rewrite E x (of_eq_true (eq_true this)))
                  _ _ _ _ _
          else
            simp_all
      have := go ((grammar E k h).rewriteSeq xs (grammar E k h).initialWord).length
      simp only [List.take_length] at this
      rw [this]
      refine congrArg (E.rewriteWord x) ?_
      exact ih

lemma grammar_language_eq {α V T} (E : EDT0LGrammar α V T) (k : ℕ) (h : E.IsIndex k) :
    E.language = (grammar E k h).language := by
  ext1 w
  simp only [language_mem_iff, generates_iff_rewriteSeq]
  --
  let rec go : (w' : List (Symbol α (Nonterminal V k))) → (w : List α) →
      UnlabelWord w' = List.map Symbol.terminal w →
      w' = List.map Symbol.terminal w
    | [],[], h => rfl
    | a::as, b::bs, h => by
      simp_all only [unlabelWord_cons, List.map_cons, List.cons.injEq]
      obtain ⟨h1,h2⟩ := h
      split at h1
      · simp_all only [Symbol.terminal.injEq, true_and]
        exact go as bs h2
      · simp_all 
    | _::_,[],h => by
      simp at h
    | [],_::_,h => by
      change [] = _ at h
      simp at h
  --
  constructor
  · intro h'
    obtain ⟨s, h'⟩ := h'
    use s
    have p1 := grammar_normalForm E k h s
    rw [h'] at p1
    clear * - p1
    change let w' := _ ; w' = _
    intro w'
    change UnlabelWord w' = _ at p1
    exact go w' w p1
  · intro h'
    obtain ⟨s, h'⟩ := h'
    use s
    have p1 := grammar_normalForm E k h s
    rw [h'] at p1
    rw [← p1]
    clear * -
    induction w with
    | nil => rfl
    | cons x xs ih => simp_all

/- TODO: This result can be strenthened as we only every consider one case of being LULT. -/

lemma grammar_isLULT {α V T} [DecidableEq V] (E : EDT0LGrammar α V T) (k : ℕ) (h : E.IsIndex k) :
    (grammar E k h).IsLULT := by
  intro w hw
  simp only [language_mem_iff, generates_iff_rewriteSeq] at hw
  obtain ⟨s, hw⟩ := hw
  use s
  constructor
  · exact hw
  --
  intro v i hi
  left
  rw [grammar_eq_toNumberedList]
  --
  change let ww := _ ; List.count v (Word.toNumberedList ww) ≤ 1
  intro ww
  have := Word.toNumberedList_nodup ww
  rw [List.nodup_iff_count] at this
  exact this _

end FiEDT0L2LULT
end EDT0LGrammar

theorem Language.isFiniteIndexEDT0L_imp_isLULT {α} (L : Language α) (h : L.IsFiniteIndexEDT0L) :
    L.IsLULT := by
  classical
  obtain ⟨k, ⟨n, m, E, h, rfl⟩⟩ := h
  rw [EDT0LGrammar.FiEDT0L2LULT.grammar_language_eq E k h]
  refine EDT0LGrammar.lult_language_isLULT (EDT0LGrammar.FiEDT0L2LULT.grammar E k h) ?_
  exact EDT0LGrammar.FiEDT0L2LULT.grammar_isLULT E k h
