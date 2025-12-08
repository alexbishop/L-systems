/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.DeriveSequence
import LSystems.FiniteIndexEDT0L.LULT.Defs
import LSystems.Basic.List

namespace EDT0LGrammar
namespace LULTImpFiEDT0L

lemma generates_mp {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (h : E.LULTImpFiEDT0L.generates (w.map .terminal)) :
    E.generates (w.map .terminal) := by
  --
  replace ⟨s, h⟩ := deriveSeq_normal_form₂ _ h
  replace h := deriveSeq_normal_form₈ _ _ h
  replace h := (derives_iff_deriveSeq _ _ _).mpr ⟨_, h⟩
  exact h

def MapTableSequence.f {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  (i : ℕ) : status_all_nonterminals E := fun n ↦ 
  --
  let pre := E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial]
  let post := E.deriveSeq (s.drop (i + 1)) [.nonterminal n]
  --
  if h₁ : .nonterminal n ∈ pre then
    if h₂ : post.length ≤ 1 then
      if h₃ : post.length = 1 then
        match h₄ : post[0] with
        | .terminal t => .many (.letter ⟨t, by 
            have h_1 : .terminal t ∈ post := List.mem_of_getElem h₄
            subst post pre
            clear * - h₁ h_1
            have h_2 : .terminal t ∈ E.deriveSeq s [.nonterminal E.initial] := by
              have h_2 : s = s.take (i + 1) ++ s.drop (i + 1) :=
                Eq.symm (List.take_append_drop _ s)
              rw [h_2]
              rw [deriveSeq_seq_append]
              rw [deriveSeq_mem_reduce
                    E (s.drop (i + 1)) (.terminal t)
                    (E.deriveSeq (List.take (i + 1) s) [Symbol.nonterminal E.initial])]
              exact ⟨_, h₁, h_1⟩
            clear * - h_2
            have h_3 : .terminal t ∈ E.visible_symbols :=
              deriveSeq_visible E s E.initial (Symbol.terminal t) h_2
            exact visible_symbol_imp_visible_terminal E t h_3⟩)
        | .nonterminal x =>
          nomatch show False by
            replace h₄ : .nonterminal x ∈ post := List.mem_of_getElem h₄
            subst post pre
            have h₅ := deriveSeq_mem_reduce E (s.drop (i + 1))
                      (.nonterminal x)
                      (E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial])
            replace h₅ := h₅.mpr ⟨_, h₁, h₄⟩
            rw [← deriveSeq_seq_append] at h₅
            conv at h₅ =>
              lhs
              arg 2
              simp only [List.take_append_drop]
            replace ⟨_, h'⟩ := h'
            rw [h'] at h₅
            simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₅
      else
        .many .epsilon
    else
      .one
  else
    .zero


@[simp high]
lemma MapTableSequence.f_eq_one {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  (i : ℕ) (n) :
    MapTableSequence.f s h' i n = .one ↔
    (.nonterminal n ∈ (E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial])) ∧
    ((E.deriveSeq (s.drop (i + 1)) [.nonterminal n]).length > 1) := by
  constructor
  · unfold MapTableSequence.f
    simp only
    intro h
    split at h
    · rename_i h_1
      split at h
      · exfalso
        split at h
        · split at h
          · simp only [reduceCtorEq] at h
          · split at h
        · simp only [reduceCtorEq] at h
      · rename_i h_2
        exact ⟨h_1, Nat.lt_of_not_le h_2⟩
    · simp only [reduceCtorEq] at h
  · intro h
    obtain ⟨h_l, h_r⟩ := h
    unfold MapTableSequence.f
    simp only [↓reduceDIte, dite_eq_right_iff, isEmpty_Prop, not_le, IsEmpty.forall_iff, h_l, h_r]

@[simp high]
lemma MapTableSequence.f_eq_zero {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  (i : ℕ) (n) :
    MapTableSequence.f s h' i n = .zero ↔
    .nonterminal n ∉ (E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial]) := by
  constructor
  · intro h
    unfold MapTableSequence.f at h
    simp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · simp only [reduceCtorEq] at h
          · split at h
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · rename_i h'
      exact h'
  · intro h
    unfold MapTableSequence.f
    simp only [↓reduceDIte, h]

@[simp high]
lemma MapTableSequence.f_eq_epsilon {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  (i : ℕ) (n) :
    MapTableSequence.f s h' i n = .many .epsilon ↔
    (.nonterminal n ∈ (E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial])) ∧
    ((E.deriveSeq (s.drop (i + 1)) [.nonterminal n]).length = 0) := by
  constructor
  · intro h
    unfold MapTableSequence.f at h
    simp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · simp only [StatusOfNonterminal.many.injEq, reduceCtorEq] at h
          · split at h
        · rename_i h_1 h_2 h_3
          constructor
          · exact h_1
          · rw [Nat.le_one_iff_eq_zero_or_eq_one] at h_2
            obtain h_2 | h_2 := h_2
            · exact h_2
            · exfalso
              exact h_3 h_2
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · intro h
    obtain ⟨h_l, h_r⟩ := h
    unfold MapTableSequence.f
    simp only
    simp only [↓reduceDIte, zero_le, zero_ne_one, h_l, h_r]

@[simp high]
lemma MapTableSequence.f_eq_letter {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  (i : ℕ) (n) (a) :
    MapTableSequence.f s h' i n = .many (.letter a) ↔
    (.nonterminal n ∈ (E.deriveSeq (s.take (i + 1)) [.nonterminal E.initial])) ∧
    (E.deriveSeq (s.drop (i + 1)) [.nonterminal n] = [.terminal a]) := by
  constructor
  · intro h
    unfold MapTableSequence.f at h
    simp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · rename_i h_1 h_2 h_3 a' h_4
            simp only [StatusOfNonterminal.many.injEq, SmallWord.letter.injEq] at h
            obtain rfl : a' = a := by
             grind only [cases eager Subtype]
            constructor
            · exact h_1
            · have h_5 :
                  E.deriveSeq (s.drop (i + 1)) [.nonterminal n] =
                  [(E.deriveSeq (s.drop (i + 1)) [.nonterminal n])[0]] := by
                exact List.eq_getElem_of_length_eq_one _ h_3
              rw [h_4] at h_5
              exact h_5
          · split at h
        · simp only [StatusOfNonterminal.many.injEq, reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · intro h
    obtain ⟨left, right⟩ := h
    unfold MapTableSequence.f
    simp only [↓reduceDIte, List.length_cons, List.length_nil, zero_add, le_refl, left, right]
    split
    · rename_i a' ha'
      simp only [StatusOfNonterminal.many.injEq, SmallWord.letter.injEq]
      simp only [right] at ha'
      simp only [List.getElem_cons_zero, Symbol.terminal.injEq] at ha'
      exact SetLike.coe_eq_coe.mp (id (Eq.symm ha'))
    · split

@[simp]
lemma MapTableSequence.f_last {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal) :
    MapTableSequence.f s h' (s.length - 1) = fun _ ↦ .zero := by
  funext x
  simp only [MapTableSequence.f_eq_zero]
  have ⟨w, h₁⟩ := h'
  have h₂ : s ≠ [] := deriveSeq_nonempty w s h₁
  have h₃ : s.length ≠ 0 := by
    simp only [ne_eq, List.length_eq_zero_iff, not_false_eq_true, h₂]
  rw [Nat.sub_one_add_one h₃, List.take_length, h₁]
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false, not_false_eq_true]

def MapTableSequence {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal) :
    List (T × status_all_nonterminals E) :=
  s.mapIdx fun i a ↦ ⟨a, MapTableSequence.f s h' i⟩

lemma MapTableSequence_length {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal) :
    (MapTableSequence s h').length = s.length := by
  unfold MapTableSequence
  exact List.length_mapIdx

@[simp]
lemma MapTableSequence_map {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h' : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal) :
    (MapTableSequence s h').map (fun x ↦ x.1) = s := by
  have h : ∀ (i : ℕ) (h : i ≤ s.length),
      List.take i ((MapTableSequence s h').map (fun x ↦ x.1)) = List.take i s := by
    intro i hi
    induction i with
    | zero =>
      simp only [List.take_zero]
    | succ i ih =>
      replace ih := ih (Nat.le_of_succ_le hi)
      rw [← List.take_append_getElem (i := i) (by
        simp only [List.length_map]
        rw [MapTableSequence_length]
        exact hi)]
      rw [ih]
      rw [← List.take_append_getElem (i := i) hi]
      rw [List.append_cancel_left_eq]
      unfold MapTableSequence
      rw [List.getElem_map, List.getElem_mapIdx]
  replace h := h s.length (Nat.le_refl s.length)
  conv at h => lhs ; rw [← MapTableSequence_length s h', ← List.length_map (fun x ↦ x.1)]
  simp only [List.take_length] at h
  exact h

@[simp]
lemma MapTableSequence_getElem {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (s : List T)
  (h₁ : ∃ w : List α, E.deriveSeq s [.nonterminal E.initial] = w.map .terminal)
  {i : ℕ}
  {h₂ : i < (MapTableSequence s h₁).length} :
    (MapTableSequence s h₁)[i] =
      ⟨ have : i < s.length := by
          simp only [MapTableSequence_length] at h₂
          exact h₂
        s[i], MapTableSequence.f s h₁ i⟩ := by
  unfold MapTableSequence
  simp only [List.getElem_mapIdx]

lemma MapTableSequence.example {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (h₁ : E.IsLULT)
  {w : List α}
  (h₂ : E.generates (w.map .terminal)) :
    ∃ (s : List T) (h : E.deriveSeq s [.nonterminal E.initial] = w.map .terminal),
      let s' := MapTableSequence s ⟨_, h⟩
      --
      have _h₁ : s ≠ [] := deriveSeq_nonempty w s h
      have _h₂ : 0 < s.length := List.length_pos_iff.mpr _h₁
      have _h₃ : s'.length = s.length := by
        unfold s'
        unfold MapTableSequence
        exact List.length_mapIdx
      have _h₄ : 0 < s'.length := Nat.lt_of_lt_of_eq _h₂ (id (Eq.symm _h₃))
      --
      (validReplacement (fun x ↦ if x = E.initial then .one else .zero) s'[0].2 s'[0].1)
      ∧ (s'[s'.length - 1].2 = fun _ ↦ .zero)
      ∧ (∀ i (_ : i + 1 < s.length), validReplacement s'[i].2 s'[i + 1].2 s'[i + 1].1) := by
  replace ⟨s, hs, h₃⟩ := h₁ w h₂
  use s, hs
  extract_lets s' _h₁ _h₂ _h₃ _h₄
  --
  split_ands
  · have : validReplacement (fun x ↦ if x = E.initial then .one else .zero) s'[0].2 s'[0].1 := {
      valid_composition := by
        unfold s'
        simp only [MapTableSequence_getElem]
        rw [Finset.subset_iff]
        unfold status_all_nonterminals.range_at_table
        unfold status_all_nonterminals.domain
        simp only [ne_eq, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
          ite_eq_right_iff, not_and_self, Finset.filter_false, Finset.sup_empty,
          Finset.bot_eq_empty, Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ, true_and,
          IsEmpty.forall_iff, implies_true]
      expansions_match := by
        intro n
        unfold validReplacement.expressions_match'
        simp only [List.flatMap_eq_nil_iff, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        split_ifs
        · simp only
        · simp only
      nodup_ensure_one := by
        intro n hn
        unfold s' at hn
        simp only [MapTableSequence_getElem] at hn
        unfold MapTableSequence.f at hn

        rw [Finset.sum_eq_sum_diff_singleton_add
            (i := E.initial)
            (by
              simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
                Finset.mem_filter, Finset.mem_univ, and_self])]
        change
          let S := _
          ∑ x ∈ S, _ + _ = _
        extract_lets S
        have h_1 : S = ∅ := by
          unfold S
          ext1
          simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
            Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, and_not_self, Finset.notMem_empty]
        rw [h_1]
        simp only [Finset.sum_empty, zero_add]
        clear S h_1
        simp only at hn
        simp only [zero_add] at hn
        split at hn
        · rename_i h_2
          split at hn
          · split at hn
            · split at hn
              · simp only [reduceCtorEq] at hn
              · split at hn
            · simp only [reduceCtorEq] at hn
          · rename_i h_3
            replace h₃ := h₃ 1 _h₂ n
            simp only at h₃
            cases h₃
            · rename_i h₃
              simp only [containedAtMostOnce_iff_count_le_one] at h₃
              unfold s'
              simp only [MapTableSequence_getElem]
              have h_4 : s = s[0]::(s.drop 1) := by
                have ⟨a, as, h⟩ := List.ne_nil_iff_exists_cons.mp _h₁
                simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, h]
              rw [h_4] at h₃
              simp only [List.drop_one, List.take_succ_cons, List.take_zero, deriveSeq_seq_single,
                rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil, List.append_nil] at h₃
              rw [Nat.le_one_iff_eq_zero_or_eq_one] at h₃
              cases h₃
              · rename_i h₃
                exfalso
                rw [List.count_eq_zero] at h₃
                rw [h_4] at h_2
                simp only [List.drop_one, List.take_succ_cons, List.take_zero, deriveSeq_seq_single,
                  rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
                  List.append_nil] at h_2
                exact h₃ h_2
              · rename_i h₃
                exact h₃
            · rename_i h₃
              exfalso
              exact h_3 h₃
        · simp only [reduceCtorEq] at hn
      nodup_ensure_zero := by
        intro n hn x hx
        split at hx
        · rename_i hx'
          subst hx'
          unfold s' at hn
          simp only [MapTableSequence_getElem] at hn
          unfold MapTableSequence.f at hn
          simp only at hn
          split at hn
          · exfalso
            split at hn
            · split at hn
              · split at hn
                · simp only [reduceCtorEq] at hn
                · split at hn
              · simp only [reduceCtorEq] at hn
            · simp only [reduceCtorEq] at hn
          · rename_i h_1
            have h_4 : s = s[0]::(s.drop 1) := by
              have ⟨a, as, h⟩ := List.ne_nil_iff_exists_cons.mp _h₁
              simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, h]
            rw [h_4] at h_1
            simp only [zero_add, List.drop_one, List.take_succ_cons, List.take_zero,
              deriveSeq_seq_single, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
              List.append_nil] at h_1
            unfold s'
            simp only [MapTableSequence_getElem]
            exact h_1
        · simp only [reduceCtorEq] at hx
      }
    exact this
  · unfold s'
    simp only [MapTableSequence_length]
    simp only [MapTableSequence_getElem]
    unfold MapTableSequence.f
    simp only
    funext vv
    split
    · rename_i h_1
      exfalso
      simp only [Nat.sub_one_add_one (Nat.ne_zero_of_lt _h₂), List.take_length] at h_1
      rw [hs] at h_1
      simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h_1
    · rfl
  · intro i hi
    have : validReplacement s'[i].2 s'[i + 1].2 s'[i + 1].1 := {
      valid_composition := by
        unfold
          status_all_nonterminals.range_at_table
          status_all_nonterminals.domain
        rw [Finset.subset_iff]
        simp only [ne_eq, Finset.mem_sup, Finset.mem_filter, Finset.mem_univ, true_and,
          forall_exists_index, and_imp]
        unfold s'
        have hi' : i < s.length := Nat.lt_of_succ_lt hi
        simp only [MapTableSequence_getElem]
        intro x x' h_1 h_2 h_3
        simp only [MapTableSequence.f_eq_one, not_and_or] at h_1
        simp only [MapTableSequence.f_eq_zero, Decidable.not_not] at h_2
        --
        obtain h_1 | h_1 := h_1
        · exfalso
          exact h_1 h_2
        --
        rw [Nat.not_gt_eq] at h_1
        --
        by_contra contra
        simp only [not_and_or, Decidable.not_not] at contra
        obtain contra | contra := contra
        · simp only [MapTableSequence.f_eq_one] at contra
          obtain ⟨cl, cr⟩ := contra

          have h' : s.drop (i + 1) = [s[i + 1]] ++ s.drop (i + 1 + 1) := by
            simp only [List.cons_append, List.nil_append, List.getElem_cons_drop]
          rw [h', deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_single] at h_1
          unfold EDT0LGrammar.rewriteSymbol at h_1
          simp only at h_1
          rw [List.mem_iff_get] at h_3
          obtain ⟨n, h_3⟩ := h_3
          have h_4 : ((E.tables s[i + 1] x').take n)
                ++ [((E.tables s[i + 1] x').get n)]
                ++ ((E.tables s[i + 1] x').drop (n + 1)) = (E.tables s[i + 1] x') := by
            simp only [List.get_eq_getElem, List.take_append_getElem, List.take_append_drop]
          rw [← h_4, h_3] at h_1
          simp only [deriveSeq_append, List.length_append] at h_1
          --
          change
            let a := _
            let b := _
            let c := _
            a + b + c ≤ 1
            at h_1
          extract_lets a b c at h_1
          --
          have h_5 : a + b + c > 1 := by
            calc a + b + c
              _ > a + 1 + c := by
                unfold b
                simp only [gt_iff_lt, add_lt_add_iff_right, add_lt_add_iff_left, cr]
              _ ≥ 1 := NeZero.one_le
          --
          clear * - h_1 h_5
          grind only
        · simp only [MapTableSequence.f_eq_zero] at contra
          have h_4 : s.take (i + 1) ++ [s[i + 1]] = s.take (i + 1 + 1) := by
            simp only [List.take_append_getElem]
          rw [← h_4, deriveSeq_seq_append] at contra
          rw [deriveSeq_mem_reduce] at contra
          simp only [deriveSeq_seq_single, rewriteWord_cons, rewriteWord_nil, List.append_nil,
            not_exists, not_and_or] at contra
          --
          obtain contra | contra := contra (.nonterminal x')
          · exact contra h_2
          · exact contra h_3
      expansions_match := by
        intro n
        unfold validReplacement.expressions_match'
        extract_lets expanded
        unfold s'
        have hi' : i < s.length := Nat.lt_of_succ_lt hi
        simp only [MapTableSequence_getElem, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        split
        · exact .intro
        · exact .intro
        · rename_i f'' hf''
          subst expanded
          simp only [List.flatMap_eq_nil_iff]
          intro x hx
          simp only [MapTableSequence.f_eq_epsilon] at hf''
          obtain ⟨left, right⟩ := hf''
          split
          · rename_i x a
            exfalso
            have h_1 : s.drop (i + 1) = [s[i + 1]] ++ s.drop (i + 1 + 1) := by
              simp only [List.cons_append, List.nil_append, List.getElem_cons_drop]
            rw [h_1, deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_single] at right
            --
            rw [List.mem_iff_get] at hx
            obtain ⟨n', hx⟩ := hx
            have h_2 : E.tables s'[i + 1].1 n = (E.tables s'[i + 1].1 n).take n'
                ++ [(E.tables s'[i + 1].1 n).get n'] ++ (E.tables s'[i + 1].1 n).drop (n' + 1) := by
              simp only [List.get_eq_getElem, List.take_append_getElem, List.take_append_drop]
            rw [hx] at h_2
            unfold s' at h_2
            simp only [MapTableSequence_getElem] at h_2
            --
            unfold EDT0LGrammar.rewriteSymbol at right
            simp only at right
            --
            rw [h_2] at right
            simp only [deriveSeq_append] at right
            simp only [deriveSeq_terminal, List.append_assoc, List.cons_append, List.nil_append,
              List.length_append, List.length_cons, Nat.add_eq_zero, List.length_eq_zero_iff,
              one_ne_zero, and_false] at right
          · unfold s'
            simp only [MapTableSequence_getElem]
            split
            · exfalso
              rename_i x1 x2 x3 hx'' h_3
              have h_1 : s.drop (i + 1) = [s[i + 1]] ++ s.drop (i + 1 + 1) := by
                simp only [List.cons_append, List.nil_append, List.getElem_cons_drop]
              rw [h_1, deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_single] at right
              simp only [MapTableSequence.f_eq_letter] at h_3
              obtain ⟨h_l, h_r⟩ := h_3
              rw [List.mem_iff_get] at hx
              --
              obtain ⟨n', hx⟩ := hx
              have h_2 : E.tables s'[i + 1].1 n = 
                  (E.tables s'[i + 1].1 n).take n' ++ [(E.tables s'[i + 1].1 n).get n']
                  ++ (E.tables s'[i + 1].1 n).drop (n' + 1) := by
                simp only [List.get_eq_getElem, List.take_append_getElem, List.take_append_drop]
              rw [hx] at h_2
              --
              unfold EDT0LGrammar.rewriteSymbol at right
              simp only at right
              --
              unfold s' at h_2
              simp only [MapTableSequence_getElem] at h_2
              --
              rw [h_2] at right
              simp only [deriveSeq_append] at right
              rw [h_r] at right
              simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
                List.length_cons, Nat.add_eq_zero, List.length_eq_zero_iff, one_ne_zero,
                and_false] at right
            · rfl
        · rename_i a' ha'
          subst expanded
          simp only [MapTableSequence.f_eq_letter] at ha'
          obtain ⟨ha'_l, ha'_r⟩ := ha'
          unfold s'
          conv => lhs; arg 2; simp only [MapTableSequence_getElem, hi]
          --
          have h_1 : .terminal a' ∈ E.deriveSeq (List.drop (i + 1) s) [Symbol.nonterminal n] := by
            rw [ha'_r]
            simp only [List.mem_cons, List.not_mem_nil, or_false]
          --
          have h_2 : s.drop (i + 1) = [s[i + 1]] ++ s.drop (i + 1 + 1) := by
            simp only [List.cons_append, List.nil_append, List.getElem_cons_drop]
          rw [h_2, deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_single] at h_1
          --
          have ⟨x', h_3, h_4⟩ := (deriveSeq_mem_reduce _ _ _ _).mp h_1
          --
          rw [List.mem_iff_get] at h_3
          obtain ⟨n', h_3⟩ := h_3
          --
          have h_5 : E.rewriteSymbol s[i + 1] (Symbol.nonterminal n)
            = (E.rewriteSymbol s[i + 1] (Symbol.nonterminal n)).take n'
              ++ [(E.rewriteSymbol s[i + 1] (Symbol.nonterminal n)).get n']
              ++ (E.rewriteSymbol s[i + 1] (Symbol.nonterminal n)).drop (n' + 1) := by
            simp only [rewriteSymbol_nonterminal, List.get_eq_getElem, List.take_append_getElem,
              List.take_append_drop]
          rw [h_3] at h_5
          clear h_3
          --
          clear * - h₃ hi hi' ha'_r ha'_l h_2 h_4 h_5 hs
          --
          -- Working with h_4
          rw [List.mem_iff_get] at h_4
          obtain ⟨n4, h4⟩ := h_4
          have h4' :
            E.deriveSeq (List.drop (i + 1 + 1) s) [x'] =
            (E.deriveSeq (List.drop (i + 1 + 1) s) [x']).take n4
            ++ [(E.deriveSeq (List.drop (i + 1 + 1) s) [x']).get n4]
            ++ (E.deriveSeq (List.drop (i + 1 + 1) s) [x']).drop (n4 + 1) := by
            simp only [List.get_eq_getElem, List.take_append_getElem, List.take_append_drop]
          rw [h4] at h4'
          clear h4
          -- working with ha'_r
          rw [h_2] at ha'_r
          clear h_2
          simp only [deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_single] at ha'_r
          unfold EDT0LGrammar.rewriteSymbol at ha'_r
          simp only at ha'_r
          -- working with h_5
          unfold EDT0LGrammar.rewriteSymbol at h_5
          simp only at h_5
          -- working with the goal
          change
            let P := _
            List.flatMap P _ = _
          extract_lets P
          --
          rw [h_5]
          simp only [List.flatMap_append, List.flatMap_singleton]
          -- Lets split the theorem into 3 goals
          have goal1 : P x' = [↑a'] := by
            cases x'
            · rename_i a''
              clear * - h4'
              simp only [deriveSeq_terminal, List.drop_succ_cons, List.drop_nil,
                List.append_nil] at h4'
              have : a'' = ↑a' := by
                by_contra contra
                have h₁ : .terminal ↑a' ∉ [(.terminal a'' : Symbol α V)] := by
                  intro contra2
                  simp only [List.mem_cons, Symbol.terminal.injEq, List.not_mem_nil,
                    or_false] at contra2
                  exact contra (id (Eq.symm contra2))
                have h₂ : (.terminal ↑a' : Symbol α V) ∈
                    (List.take ↑n4 [.terminal a'']) ++ [(.terminal ↑a' : Symbol α V)] := by
                  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
                rw [h4'] at h₁
                exact h₁ h₂
              subst a'' P
              simp only
            · rename_i v
              let fv := MapTableSequence.f _ ⟨_, hs⟩ (i + 1) v
              if h_fv : fv = .many (.letter a') then
                unfold P
                simp only
                unfold fv at h_fv
                simp only [MapTableSequence_getElem, h_fv]
              else
                -- by_contra main_contra
                exfalso
                cases h_fv' : fv
                · unfold fv at h_fv'
                  simp only [MapTableSequence.f_eq_zero] at h_fv'
                  clear * - ha'_l hi ha'_l h_5 h_fv'
                  --
                  have h₁ : s.take (i + 1 + 1) = s.take (i + 1) ++ [s[i + 1]] := by
                    simp only [List.take_append_getElem]
                  --
                  rw [h₁] at h_fv'
                  clear h₁
                  simp only [deriveSeq_seq_append, deriveSeq_seq_single] at h_fv'
                  rw [rewriteWord_nonterminal_mem] at h_fv'
                  simp only [not_exists] at h_fv'
                  --
                  replace h_fv' := h_fv' n ha'_l
                  have contra : .nonterminal v ∈ E.tables s[i + 1] n := by
                    rw [h_5]
                    simp only [List.append_assoc, List.cons_append, List.nil_append,
                      List.mem_append, List.mem_cons, true_or, or_true]
                  --
                  exact h_fv' contra
                · unfold fv at h_fv'
                  simp only [MapTableSequence.f_eq_one] at h_fv'
                  obtain ⟨left, right⟩ := h_fv'
                  clear * - right h4' ha'_r h_5
                  replace ha'_r := congrArg List.length ha'_r
                  rw [h_5] at ha'_r
                  simp only [deriveSeq_append, List.length_append] at ha'_r
                  --
                  change
                    let a := _
                    let b := _
                    let c := _
                    a + b + c = _
                    at ha'_r
                  extract_lets a b c at ha'_r
                  --
                  have h₁ : a + b + c > 1 := by
                    calc a + b + c
                      _ ≥ a + b := Nat.le_add_right (a + b) c
                      _ ≥ b := Nat.le_add_left b a
                      _ > 1 := right
                  rw [ha'_r] at h₁
                  simp only [List.length_cons, List.length_nil, zero_add, gt_iff_lt,
                    lt_self_iff_false] at h₁
                · rename_i ww
                  cases h_fv'_ww : ww
                  · subst ww
                    unfold fv at h_fv'
                    simp only [MapTableSequence.f_eq_epsilon] at h_fv'
                    obtain ⟨left, right⟩ := h_fv'
                    rw [List.length_eq_zero_iff] at right
                    simp only [right] at h4'
                    simp only [List.take_nil, List.nil_append, List.drop_nil, List.append_nil,
                      List.ne_cons_self] at h4'
                  · rename_i a''
                    subst ww
                    have h_a'': a'' ≠ a' := by
                      clear * - h_fv' h_fv
                      intro contra
                      subst a''
                      exact h_fv h_fv'
                    unfold fv at h_fv'
                    simp only [MapTableSequence.f_eq_letter] at h_fv'
                    obtain ⟨left, right⟩ := h_fv'
                    clear * - left right h_a'' ha'_r h_5
                    have h₁ : .nonterminal v ∈ E.tables s[i + 1] n := by
                      rw [h_5]
                      simp only [List.append_assoc, List.cons_append, List.nil_append,
                        List.mem_append, List.mem_cons, true_or, or_true]
                    clear h_5
                    --
                    have h₂: (.terminal ↑a'' : Symbol α V) ∈
                        E.deriveSeq (List.drop (i + 1 + 1) s) (E.tables s[i + 1] n) := by
                      rw [deriveSeq_mem_reduce]
                      use .nonterminal v, h₁
                      rw [right]
                      simp only [List.mem_cons, List.not_mem_nil, or_false]
                    --
                    rw [ha'_r] at h₂
                    simp only [List.mem_cons, Symbol.terminal.injEq, SetLike.coe_eq_coe,
                      List.not_mem_nil, or_false] at h₂
                    exact h_a'' h₂
          rw [goal1]
          clear goal1
          --
          have goal2 : List.flatMap P (List.take (↑n') (E.tables s[i + 1] n)) = [] := by
            simp only [rewriteSymbol_nonterminal, List.flatMap_eq_nil_iff]
            intro x hx
            subst P
            simp only
            split
            · rename_i a''
              exfalso
              simp only [List.mem_iff_factor] at hx
              obtain ⟨n'', hx⟩ := hx
              rw [hx] at h_5
              rw [h_5] at ha'_r
              simp only [deriveSeq_append] at ha'_r
              rw [h4'] at ha'_r
              simp only [deriveSeq_terminal] at ha'_r
              clear * - ha'_r
              simp only [← List.append_assoc] at ha'_r
              change
                let a := _
                let b := _
                let c := _
                let d := _
                let e := _
                let f := _
                a ++ b ++ c ++ d ++ [.terminal ↑a'] ++ e ++ f
                  = [(.terminal ↑a' : Symbol α V)]
                at ha'_r
              extract_lets a b c d e f at ha'_r
              --
              have h₁ : (a ++ b ++ c ++ d) ++ [.terminal ↑a'] ++ (e ++ f) = [.terminal ↑a'] := by
                simp only [← List.append_assoc]
                exact ha'_r
              --
              rw [List.append_cancel_middle] at h₁
              simp only [List.append_assoc, List.append_eq_nil_iff, reduceCtorEq, false_and,
                and_false] at h₁
            · rename_i x''
              split
              · rename_i a'' heq
                exfalso
                simp only [MapTableSequence_getElem, f_eq_letter] at heq
                obtain ⟨heq_l, heq_r⟩ := heq
                --
                simp only [List.mem_iff_factor] at hx
                obtain ⟨n'', hx⟩ := hx
                --
                rw [h_5, hx] at ha'_r
                --
                simp only [deriveSeq_append] at ha'_r
                rw [h4', heq_r] at ha'_r
                simp only [← List.append_assoc] at ha'_r
                change
                  let a := _
                  let b := _
                  let c := _
                  let d := _
                  let e := _
                  let f := _
                  a ++ b ++ c ++ d ++ [.terminal ↑a'] ++ e ++ f
                    = [(.terminal ↑a' : Symbol α V)]
                  at ha'_r
                extract_lets a b c d e f at ha'_r
                have h₁ : (a ++ b ++ c ++ d) ++ [.terminal ↑a'] ++ (e ++ f) = [.terminal ↑a'] := by
                  simp only [← List.append_assoc]
                  exact ha'_r
                --
                rw [List.append_cancel_middle] at h₁
                simp only [List.append_assoc, List.append_eq_nil_iff, reduceCtorEq, false_and,
                  and_false] at h₁
              · rfl
          --
          have goal3 : List.flatMap P (List.drop (↑n' + 1) (E.tables s[i + 1] n)) = [] := by
            simp only [rewriteSymbol_nonterminal, List.flatMap_eq_nil_iff]
            intro x hx
            subst P
            simp only
            split
            · rename_i a''
              exfalso
              simp only [List.mem_iff_factor] at hx
              obtain ⟨n'', hx⟩ := hx
              rw [hx] at h_5
              rw [h_5] at ha'_r
              simp only [deriveSeq_append] at ha'_r
              rw [h4'] at ha'_r
              simp only [deriveSeq_terminal] at ha'_r
              clear * - ha'_r
              simp only [← List.append_assoc] at ha'_r
              change
                let a := _
                let b := _
                let c := _
                let d := _
                let e := _
                let f := _
                a ++ b ++ [.terminal ↑a'] ++ c ++ d ++ e ++ f
                  = [(.terminal ↑a' : Symbol α V)]
                at ha'_r
              extract_lets a b c d e f at ha'_r
              --
              have h₁ : (a ++ b) ++ [.terminal ↑a'] ++ (c ++ d ++ e ++ f) = [.terminal ↑a'] := by
                simp only [← List.append_assoc]
                exact ha'_r
              --
              rw [List.append_cancel_middle] at h₁
              simp only [List.append_assoc, List.append_eq_nil_iff, reduceCtorEq, false_and,
                and_false] at h₁
            · rename_i x''
              split
              · rename_i a'' heq
                exfalso
                simp only [MapTableSequence_getElem, f_eq_letter] at heq
                obtain ⟨heq_l, heq_r⟩ := heq
                --
                simp only [List.mem_iff_factor] at hx
                obtain ⟨n'', hx⟩ := hx
                --
                rw [h_5, hx] at ha'_r
                --
                simp only [deriveSeq_append] at ha'_r
                rw [h4', heq_r] at ha'_r
                simp only [← List.append_assoc] at ha'_r
                change
                  let a := _
                  let b := _
                  let c := _
                  let d := _
                  let e := _
                  let f := _
                  a ++ b ++ [.terminal ↑a'] ++ c ++ d ++ e ++ f
                    = [(.terminal ↑a' : Symbol α V)]
                  at ha'_r
                extract_lets a b c d e f at ha'_r
                --
                have h₁ : (a ++ b) ++ [.terminal ↑a'] ++ (c ++ d ++ e ++ f) = [.terminal ↑a'] := by
                  simp only [← List.append_assoc]
                  exact ha'_r
                --
                rw [List.append_cancel_middle] at h₁
                simp only [List.append_assoc, List.append_eq_nil_iff, reduceCtorEq, false_and,
                  and_false] at h₁
              · rfl

          rw [goal2, goal3]
          simp only [List.nil_append, List.append_nil]
      nodup_ensure_one := by
        intro v h_1
        unfold s'
        have hi' : i < s.length := Nat.lt_of_succ_lt hi
        simp only [MapTableSequence_getElem]
        unfold s' at h_1
        simp only [MapTableSequence_getElem, MapTableSequence.f_eq_one] at h_1
        simp only [Finset.sum_nat_eq_one]
        --
        obtain ⟨h_1l, h_1r⟩ := h_1
        --
        have h₁ : s.take (i + 1 + 1) = s.take (i + 1) ++ [s[i + 1]] := by
          simp only [List.take_append_getElem]
        rw [h₁] at h_1l
        rw [deriveSeq_seq_append, deriveSeq_seq_single, rewriteWord_nonterminal_mem] at h_1l
        --
        obtain ⟨y, hy, hy'⟩ := h_1l
        --
        use y
        use (by
          simp only [f_eq_one, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact hy
          · rw [List.mem_iff_factor] at hy'
            obtain ⟨n'', hy'⟩ := hy'
            have h₂ : s.drop (i + 1) = [s[i + 1]] ++ s.drop (i + 1 + 1) := by
              simp only [List.cons_append, List.nil_append, List.getElem_cons_drop]
            rw [h₂, deriveSeq_seq_append, deriveSeq_seq_single]
            rw [rewriteWord_single]
            unfold EDT0LGrammar.rewriteSymbol
            simp only
            rw [hy']
            simp only [deriveSeq_append, List.length_append]
            --
            change
              let a := _
              let b := _
              let c := _
              a + b + c > 1
            extract_lets a b c
            --
            calc a + b + c
              _ ≥ b + c := by
                simp only [ge_iff_le, add_le_add_iff_right, le_add_iff_nonneg_left, zero_le]
              _ ≥ b := by
                simp only [ge_iff_le, le_add_iff_nonneg_right, zero_le]
              _ > 1 := h_1r)
        have h₅ := h₃ (i + 1 + 1) hi v
        simp only at h₅
        constructor
        · obtain h₅ | h₅ := h₅
          · simp only [containedAtMostOnce_iff_count_le_one] at h₅
            match h'' : List.count (Symbol.nonterminal v) (E.tables s[i + 1] y) with
            | 1 => rfl
            | 0 =>
              exfalso
              clear * - h'' hy'
              have : .nonterminal v ∉ E.tables s[i + 1] y := List.count_eq_zero.mp h''
              exact this hy'
            | n + 2 =>
              have h₃ := h₃ (i + 1 + 1) hi v
              simp only [containedAtMostOnce_iff_count_le_one] at h₃
              obtain h₃ | h₃ := h₃
              · exfalso
                have h₇ : s.take (i + 1 + 1) = s.take (i + 1) ++ [s[i + 1]] := by
                  simp only [List.take_append_getElem]
                rw [h₇] at h₃
                simp only [deriveSeq_seq_append, deriveSeq_seq_single] at h₃
                rw [List.mem_iff_factor] at hy
                obtain ⟨nnn, hy⟩ := hy
                rw [hy] at h₃
                simp only [rewriteWord_append, List.count_append] at h₃
                clear * - h₃ h''
                --
                change
                  let a := _
                  let b := _
                  let c := _
                  a + b + c ≤ 1
                  at h₃
                extract_lets a b c at h₃
                --
                have contra : a + b + c > 1 := by
                  calc a + b + c
                    _ ≥ a + b := Nat.le_add_right (a + b) c
                    _ ≥ b := Nat.le_add_left b a
                    _ > 1 := by
                      unfold b
                      rw [rewriteWord_single]
                      unfold EDT0LGrammar.rewriteSymbol
                      simp only
                      rw [h'']
                      simp only [Nat.succ_eq_add_one, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
                        zero_lt_one, or_true]
                --
                grind only
              · clear * - h₃ h_1r
                exfalso
                grind only
          · exfalso
            clear * - h₅ h_1r
            grind only
        · intro Y hY hY'
          simp only [f_eq_one, gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hY
          --
          obtain ⟨hY_l, hY_r⟩ := hY

          obtain ⟨A,B,C,H⟩ | ⟨A,B,C,H⟩ := List.contains_two
            (by
              simp only [ne_eq, Symbol.nonterminal.injEq]
              exact hY') hY_l hy
          · have H' := congrArg (fun x ↦ E.rewriteWord s[i + 1] x) H
            simp only [rewriteWord_append] at H'
            by_contra contra
            --
            have hh : .nonterminal v ∈ E.tables s[i + 1] Y := by
              by_contra contra2
              rw [← List.count_eq_zero] at contra2
              exact contra contra2
            --
            rw [List.mem_iff_factor] at hh
            rw [List.mem_iff_factor] at hy'
            --
            obtain ⟨N1, H1⟩ := hh
            obtain ⟨N2, H2⟩ := hy'
            --
            simp only [rewriteWord_single] at H'
            unfold EDT0LGrammar.rewriteSymbol at H'
            simp only at H'
            rw [H1, H2] at H'
            --
            conv at H' =>
              lhs
              simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append]
              arg 2
              simp only [List.take_append_getElem]
            --
            obtain h₅ | h₅ := h₅
            · simp only [containedAtMostOnce_iff_count_le_one] at h₅
              rw [H'] at h₅
              simp only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
                List.count_cons_self] at h₅
              simp only [← Nat.add_assoc] at h₅
              clear * - h₅
              grind only
            · clear * - h_1r h₅
              grind only

          · have H' := congrArg (fun x ↦ E.rewriteWord s[i + 1] x) H
            simp only [rewriteWord_append] at H'
            by_contra contra
            --
            have hh : .nonterminal v ∈ E.tables s[i + 1] Y := by
              by_contra contra2
              rw [← List.count_eq_zero] at contra2
              exact contra contra2
            --
            rw [List.mem_iff_factor] at hh
            rw [List.mem_iff_factor] at hy'
            --
            obtain ⟨N1, H1⟩ := hh
            obtain ⟨N2, H2⟩ := hy'
            --
            simp only [rewriteWord_single] at H'
            unfold EDT0LGrammar.rewriteSymbol at H'
            simp only at H'
            rw [H1, H2] at H'
            --
            conv at H' =>
              lhs
              simp only [← deriveSeq_seq_single, ← deriveSeq_seq_append]
              arg 2
              simp only [List.take_append_getElem]
            --
            obtain h₅ | h₅ := h₅
            · simp only [containedAtMostOnce_iff_count_le_one] at h₅
              rw [H'] at h₅
              simp only [List.append_assoc, List.cons_append, List.nil_append, List.count_append,
                List.count_cons_self] at h₅
              simp only [← Nat.add_assoc] at h₅
              clear * - h₅
              grind only
            · clear * - h_1r h₅
              grind only
      nodup_ensure_zero := by
        intro v h_1 v' h_2 h_3
        unfold s' at h_1
        simp only [MapTableSequence_getElem] at h_1
        simp only [MapTableSequence.f_eq_zero] at h_1
        --
        have hi' : i < s.length := Nat.lt_of_succ_lt hi
        --
        unfold s' at h_2
        simp only [MapTableSequence_getElem] at h_2
        simp only [MapTableSequence.f_eq_one] at h_2
        obtain ⟨h_2_l, h_2_r⟩ := h_2
        --
        unfold s' at h_3
        simp only [MapTableSequence_getElem] at h_3
        --
        have h₆ : s.take (i + 1 + 1) = s.take (i + 1) ++ [s[i + 1]] := by
          simp only [List.take_append_getElem]
        rw [h₆] at h_1
        --
        rw [deriveSeq_seq_append, deriveSeq_seq_single] at h_1
        --
        simp only [List.mem_iff_factor] at h_2_l
        obtain ⟨s2, h_2_l⟩ := h_2_l
        --
        rw [h_2_l] at h_1
        simp only [rewriteWord_append] at h_1
        change
          let ab := _
          _ ∉ ab
          at h_1
        extract_lets ab at h_1
        --
        have contra : .nonterminal v ∈ ab := by
          subst ab
          simp only [List.append_assoc, List.mem_append]
          right
          left
          rw [rewriteWord_single]
          unfold EDT0LGrammar.rewriteSymbol
          simp only
          exact h_3
        --
        exact h_1 contra
      }
    exact this

lemma generates_mpr {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List α)
  (h₁ : E.IsLULT)
  (h₂ : E.generates (w.map .terminal)) :
    E.LULTImpFiEDT0L.generates (w.map .terminal) := by
  have ⟨s, hs, h, h', h''⟩ := MapTableSequence.example h₁ h₂
  have s_nonempty := deriveSeq_nonempty _ _ hs
  simp only [← MapTableSequence_length s ⟨w,hs⟩] at h''
  have hh := deriveSeq_normal_form₇ _ (by
    have hh := MapTableSequence_length s ⟨w,hs⟩
    rw [hh]
    replace hh := deriveSeq_nonempty _ _ hs
    exact List.length_pos_iff.mpr hh) h h''
  --
  replace ⟨l, r⟩ := hh (s.length - 1) (by
    rw [MapTableSequence_length s ⟨w,hs⟩]
    simp only [tsub_lt_self_iff, zero_lt_one, and_true]
    replace hh := deriveSeq_nonempty _ _ hs
    exact List.length_pos_iff.mpr hh)
  --
  simp only [MapTableSequence_map] at r
  simp only [MapTableSequence_getElem] at r
  --
  replace s_nonempty : s.length ≠ 0 := by
    simp only [ne_eq, List.length_eq_zero_iff]
    exact s_nonempty
  simp only [Nat.sub_one_add_one s_nonempty] at r
  --
  simp only [List.take_length] at r
  --
  have h₃ : (List.map (fun x ↦ Table.step x.1 x.2) (MapTableSequence s ⟨w,hs⟩)).length
          = s.length := by
    simp only [List.length_map, MapTableSequence_length]
  conv at r => rhs ; rw [← h₃]
  
  simp only [Nat.sub_one_add_one s_nonempty] at l
  conv at l =>
    arg 1
    arg 2
    simp only [← h₃]
  simp only [List.take_length] at l
  --
  simp only [List.take_length] at r
  simp only [hs] at r
  --
  conv at r => lhs; simp only [mapByStatus_terminals]
  --
  simp only [MapTableSequence_getElem, MapTableSequence.f_last] at l
  --
  have ⟨s'', h''⟩ := normalForm_step_decomposition' l
  rw [h''] at r
  simp only [deannotateWord_append, deannotateWord_terminals, deannotateWord_ender,
    List.append_nil] at r
  --
  let rec helper (u v : List α)
      (h : (u.map .terminal : List (Symbol α V)) = v.map .terminal) : u = v := by
    match u, v with
    | .nil, .nil => rfl
    | a::as, b::bs =>
      simp only [List.map_cons, List.cons.injEq, Symbol.terminal.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [helper _ _ h]
    | a::as, .nil =>
      exfalso
      simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
    | .nil, b::bs =>
      exfalso
      simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
  --
  have := helper _ _ r
  subst s''
  --
  clear helper
  --
  let rec helper2 (u v : List α)
      (h : (u.map .terminal : List (annotated_symbols E)) = v.map .terminal) : u = v := by
    match u, v with
    | .nil, .nil => rfl
    | a::as, b::bs =>
      simp only [List.map_cons, List.cons.injEq, Symbol.terminal.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [helper2 _ _ h]
    | a::as, .nil =>
      exfalso
      simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
    | .nil, b::bs =>
      exfalso
      simp only [List.map_cons, List.map_nil, reduceCtorEq] at h
  --
  have ⟨s'', h_10, h_11⟩ := normalForm_step_rewrite_final₁ _ l
  rw [h''] at h_10
  simp only [List.append_cancel_right_eq] at h_10
  --
  have := helper2 _ _ h_10
  subst s''
  --
  rw [← deriveSeq_seq_single, ← deriveSeq_seq_append] at h_11
  have h_12 := (derives_iff_deriveSeq _ _ _).mpr ⟨_, h_11⟩
  clear * - h_12
  exact h_12

lemma generates_iff {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (w : List T)
  (h₁ : E.IsLULT) :
    E.LULTImpFiEDT0L.generates (w.map .terminal) ↔ E.generates (w.map .terminal) :=
  ⟨generates_mp w, generates_mpr w h₁⟩

end LULTImpFiEDT0L
end EDT0LGrammar
