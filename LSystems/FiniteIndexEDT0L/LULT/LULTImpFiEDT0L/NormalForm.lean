/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L.Defs
import LSystems.EDT0L.Basic
import LSystems.Basic.Finset

namespace EDT0LGrammar
namespace LULTImpFiEDT0L

@[simp]
def normalForm.stepP.used_nonterminals' {α V T : Type*} [Fintype V] [Fintype T] [DecidableEq α]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (s : annotated_nonterminals E) : Prop :=
  match s with
  | .single _ g => f = g
  | .ender g => f = g
  | _ => false

variable {α V T : Type*} [Fintype V] [Fintype T] [DecidableEq α]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (s : annotated_nonterminals E) in
instance : Decidable (normalForm.stepP.used_nonterminals' f s) := by
  unfold normalForm.stepP.used_nonterminals'
  split <;> exact inferInstance

namespace normalForm
variable {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))

def startP := w = [.nonterminal .start]

def deadP := ∃ s : List α, w = s.map .terminal ++ [.nonterminal .dead]

def outputP := ∃ s : List α, w = s.map .terminal

structure stepP (f : status_all_nonterminals E) : Prop where
  nonempty :
    w ≠ []
  nodup_nonterminals :
    ∀ n, w.count (.nonterminal n) ≤ 1
  used_nonterminal :
    ∀ x (_ : .nonterminal x ∈ w), normalForm.stepP.used_nonterminals' f x
  used_nonterminal' :
    ∀ {x}, .nonterminal (.single x f) ∈ w ↔ f x = .one
  last_is_ender : w.getLast nonempty = .nonterminal (.ender f)

end normalForm

inductive normalForm {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) : Prop where
| start (h : normalForm.startP w)
| dead (h : normalForm.deadP w)
| output (h : normalForm.outputP w)
| step (h : ∃ f, normalForm.stepP w f)

lemma normalForm_start_imp_not_dead {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.startP w) :
    ¬ normalForm.deadP w := by
  intro contra
  obtain ⟨s, contra⟩ := contra
  have h₁ : .nonterminal .dead ∈ w := by
    rw [contra]
    simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, List.mem_cons,
      List.not_mem_nil, or_false, or_true]
  obtain rfl := h
  simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil, or_self] at h₁

lemma normalForm_start_imp_not_output {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.startP w) :
    ¬ normalForm.outputP w := by
  have h₁ : .nonterminal .start ∈ w := by
    obtain rfl := h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro contra
  obtain ⟨s, rfl⟩ := contra
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁

lemma normalForm_start_imp_not_step {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.startP w) {f} :
    ¬ normalForm.stepP w f := by
  intro contra
  have h₁ : .nonterminal (.ender f) ∈ w := by
    rw [← w.take_append_getLast contra.nonempty, contra.last_is_ender]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  obtain rfl := h
  simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil, or_self] at h₁

lemma normalForm_dead_imp_not_start {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w) :
    ¬ normalForm.startP w := by
  intro contra
  revert h
  exact normalForm_start_imp_not_dead E w contra

lemma normalForm_dead_imp_not_output {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w) :
    ¬ normalForm.outputP w := by
  intro contra
  have h₁ : .nonterminal .dead ∈ w := by
    obtain ⟨s, rfl⟩ := h
    simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, List.mem_cons,
      List.not_mem_nil, or_false, or_true]
  obtain ⟨s, rfl⟩ := contra
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁

lemma normalForm_dead_imp_not_step {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w) {f} :
    ¬ normalForm.stepP w f := by
  intro contra
  have h₁ : .nonterminal (.ender f) ∈ w := by
    rw [← w.take_append_getLast contra.nonempty, contra.last_is_ender]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  obtain ⟨s, rfl⟩ := h
  simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, List.mem_cons,
    Symbol.nonterminal.injEq, List.not_mem_nil, or_self] at h₁

lemma normalForm_output_imp_not_start {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w) :
    ¬ normalForm.startP w := by
  intro contra
  revert h
  exact normalForm_start_imp_not_output E w contra

lemma normalForm_output_imp_not_dead {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w) :
    ¬ normalForm.deadP w := by
  intro contra
  revert h
  exact normalForm_dead_imp_not_output E w contra

lemma normalForm_output_imp_not_step {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w) {f} :
    ¬ normalForm.stepP w f := by
  intro contra
  have h₁ : .nonterminal (.ender f) ∈ w := by
    rw [← w.take_append_getLast contra.nonempty, contra.last_is_ender]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  obtain ⟨s, rfl⟩ := h
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at h₁

lemma normalForm_step_imp_not_start {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) :
    ¬ normalForm.startP w := by
  intro contra
  revert h
  exact normalForm_start_imp_not_step E w contra

lemma normalForm_step_imp_not_output {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) :
    ¬ normalForm.outputP w := by
  intro contra
  revert h
  exact normalForm_output_imp_not_step E w contra

lemma normalForm_step_imp_not_dead {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) :
    ¬ normalForm.deadP w := by
  intro contra
  revert h
  exact normalForm_dead_imp_not_step E w contra

lemma normalForm_start_count {α V T : Type*} [Fintype V] [Fintype T] [DecidableEq α]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.startP w) :
    w.countP EDT0LGrammar.SymbolIsNonterminal = 1 := by
  obtain rfl := h
  simp only [SymbolIsNonterminal_nonterminal, List.countP_cons_of_pos, List.countP_nil, zero_add]

lemma normalForm_dead_count {α V T : Type*} [Fintype V] [Fintype T] [DecidableEq α]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w) :
    w.countP EDT0LGrammar.SymbolIsNonterminal = 1 := by
  obtain ⟨s, rfl⟩ := h
  simp only [List.countP_append, List.countP_map, SymbolIsNonterminal_nonterminal,
    List.countP_cons_of_pos, List.countP_nil, zero_add, Nat.add_eq_right, List.countP_eq_zero,
    Function.comp_apply, SymbolIsNonterminal_terminal, Bool.false_eq_true, not_false_eq_true,
    implies_true]

lemma normalForm_output_count {α V T : Type*} [Fintype V] [Fintype T] [DecidableEq α]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w) :
    w.countP EDT0LGrammar.SymbolIsNonterminal = 0 := by
  obtain ⟨s, rfl⟩ := h
  simp only [List.countP_map, List.countP_eq_zero, Function.comp_apply,
    SymbolIsNonterminal_terminal, Bool.false_eq_true, not_false_eq_true, implies_true]

lemma normalForm_step_count {α V T : Type*}
  [finV : Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) :
    w.countP EDT0LGrammar.SymbolIsNonterminal ≤ (Fintype.card V) + 1 := by
  let s : Finset (annotated_nonterminals E) :=
    { s | normalForm.stepP.used_nonterminals' f s}
  --
  let embed : V ⊕ Unit ↪ annotated_nonterminals E := {
    toFun := fun x ↦
      match x with
      | .inl v => .single v f
      | .inr _ => .ender f
    inj' := by
      intro a₁ a₂ h₁
      simp only at h₁
      split at h₁
      · split at h₁
        · simp_all only [Nonterminal.single.injEq, and_true]
        · exfalso
          simp only [reduceCtorEq] at h₁
      · split at h₁
        · exfalso
          simp only [reduceCtorEq] at h₁
        · simp_all only
    }
  --
  let fin : Fintype (V ⊕ Unit) := instFintypeSum V Unit
  --
  have h₁ : s = fin.elems.map embed := by
    unfold s
    clear s
    change
      let t₁ := _
      let t₂ := _
      t₁ = t₂
    extract_lets t₁ t₂
    --
    have h₁ : ∀ s, s ∈ t₁ ↔ s ∈ t₂ := by
      intro s
      subst t₁ t₂
      unfold embed
      constructor
      · intro h₁
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁
        unfold normalForm.stepP.used_nonterminals' at h₁
        split at h₁
        · rename_i s' b' g'
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Sum.exists,
            Nonterminal.single.injEq, ↓existsAndEq, true_and, reduceCtorEq, and_false, exists_const,
            or_false]
          constructor
          · exact Fintype.complete (Sum.inl b')
          · exact h₁
        · simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Sum.exists, reduceCtorEq,
            and_false, exists_false, Nonterminal.ender.injEq, exists_and_right, false_or]
          constructor
          · use .unit
            exact Fintype.complete (Sum.inr ())
          · exact h₁
        · exfalso
          simp only [Bool.false_eq_true] at h₁
      · simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Sum.exists, exists_and_right,
          Finset.mem_filter, Finset.mem_univ, true_and]
        intro a
        cases a with
        | inl h_1 =>
          obtain ⟨w_1, h_1⟩ := h_1
          obtain ⟨left, right⟩ := h_1
          subst right
          rfl
        | inr h_2 =>
          obtain ⟨left, right⟩ := h_2
          obtain ⟨w_1, h_1⟩ := left
          subst right
          rfl
    exact Finset.ext_iff.mpr h₁
  --
  have h₂ : s.card = (Fintype.card V) + 1 := by
    rw [h₁]
    simp only [Finset.card_map]
    change Fintype.card (V ⊕ Unit) = _
    simp only [Fintype.card_sum, Fintype.card_unique]
  --
  rw [List.countP_eq_length_filter]
  rw [← List.sum_toFinset_count_eq_length]
  --
  let s₁ : Finset (annotated_symbols E) := (List.filter SymbolIsNonterminal w).toFinset
  let s₂ : Finset (annotated_nonterminals E) := {x | .nonterminal x ∈ w}
  --
  let f : annotated_symbols E → ℕ := fun x ↦ List.count x (List.filter SymbolIsNonterminal w)
  let g : annotated_nonterminals E → ℕ := fun _ ↦ 1

  have h₃ := Finset.sum_bij' (s := s₁) (t := s₂) (f := f) (g := g)
    fun x h ↦
      match x with
      | .terminal a =>
        nomatch show False by
          unfold s₁ at h
          simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset,
            SymbolIsNonterminal_terminal, Bool.false_eq_true, and_false] at h
      | .nonterminal v => v
    (by 
      intro a ha
      exact Symbol.nonterminal a )
    (by 
      intro a ha
      unfold s₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split <;> try split
      focus
      rename_i v h₃
      simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset,
        SymbolIsNonterminal_nonterminal, and_true] at h₃
      exact h₃ )
    (by
      unfold s₁ s₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.toFinset_filter,
        List.mem_toFinset, SymbolIsNonterminal_nonterminal, and_true, imp_self, implies_true] )
    (by
      intro a ha
      simp only
      split <;> try split
      focus
      rfl )
    (by
      intro a ha
      simp only )
    (by
      unfold s₁ f g
      unfold SymbolIsNonterminal
      simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset, and_imp]
      intro a ha ha'
      split at ha'
      · exfalso
        simp only [Bool.false_eq_true] at ha'
      · rename_i n
        have h₃ := h.nodup_nonterminals n
        rw [Nat.le_one_iff_eq_zero_or_eq_one] at h₃
        cases h₃
        · rename_i h₃
          exfalso
          exact List.count_eq_zero.mp h₃ ha
        · rename_i h₃
          simp only [List.count_filter, h₃] )
  --
  rw [h₃]
  clear h₃
  unfold g
  simp only [Finset.sum_const, smul_eq_mul, mul_one, ge_iff_le]
  --
  have h₃ : s₂ ⊆ s := by
    rw [Finset.subset_iff]
    unfold s s₂
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h₃ := h.used_nonterminal x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h₃
  replace h₃ : s₂.card ≤ s.card := Finset.card_le_card h₃
  rw [h₂] at h₃
  exact h₃

lemma normalForm_count {α V T : Type*}
  [finV : Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm w) :
    w.countP EDT0LGrammar.SymbolIsNonterminal ≤ (Fintype.card V) + 1 := by
  cases h
  · rename_i h
    replace h := normalForm_start_count w h
    rw [h]
    simp only [le_add_iff_nonneg_left, zero_le]
  · rename_i h
    replace h := normalForm_dead_count w h
    rw [h]
    simp only [le_add_iff_nonneg_left, zero_le]
  · rename_i h
    replace h := normalForm_output_count w h
    rw [h]
    simp only [le_add_iff_nonneg_left, zero_le]
  · rename_i h
    replace ⟨f, h⟩ := h
    replace h := normalForm_step_count w h
    exact h

lemma normalForm_step_decomposition {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)} {f}
  (h : normalForm.stepP w f) :
    ∃ s : List (V ⊕ α),
      w =
        (s.map fun x ↦
          match x with
          | .inl v => .nonterminal (.single v f)
          | .inr a => .terminal a )
        ++ [.nonterminal (.ender f)] := by
  have h₁ : w.take (w.length - 1) ++ [w.getLast h.nonempty] = w :=
    List.take_append_getLast w h.nonempty
  rw [h.last_is_ender] at h₁
  --
  have h₂ : ∀ v, .nonterminal v ∈ w.take (w.length - 1) → ∃ v', v = .single v' f := by
    intro v hv
    have h₂ : .nonterminal v ∈ w := List.mem_of_mem_take hv
    have h₃ := h.used_nonterminal _ h₂
    unfold normalForm.stepP.used_nonterminals' at h₃
    split at h₃
    · rename_i v' g
      subst g
      exact ⟨v', rfl⟩
    · exfalso
      rename_i g
      subst g
      have h₄ := h.nodup_nonterminals (.ender f)
      rw [← h₁] at h₄
      simp only [List.count_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_self, List.mem_cons, or_false, List.count_eq_one_of_mem,
        add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h₄
      rw [List.count_eq_zero] at h₄
      exact h₄ hv
    · exfalso
      simp only [Bool.false_eq_true] at h₃
  --
  let s : List (V ⊕ α) :=
    (w.take (w.length - 1)).pmap
      (P := fun x ↦ x ∈ (w.take (w.length - 1)))
      fun x hx ↦
        match x with
        | .terminal a => .inr a
        | .nonterminal (.single v _) => .inl v
        | .nonterminal (.ender _) | .nonterminal .dead | .nonterminal .start =>
          nomatch show False by
            simp only at hx
            replace ⟨_, h₂⟩ := h₂ _ hx
            simp only [reduceCtorEq] at h₂
      (fun a ha ↦ ha)
  --
  use s
  rw [← h₁]
  simp only [List.append_cancel_right_eq]
  --
  subst s
  rw [List.map_pmap]
  --
  apply Eq.symm
  rw [List.pmap_eq_self]
  --
  intro a ha
  split
  · rename_i h₃
    split at h₃
    · exfalso
      simp only [reduceCtorEq] at h₃
    · rename_i v' x hx v'' f' hv''
      simp_all only [Sum.inl.injEq, Symbol.nonterminal.injEq, Nonterminal.single.injEq, true_and]
      have h₄ : .nonterminal (.single v' f') ∈ w := List.mem_of_mem_take hv''
      have h₅ := h.used_nonterminal _ h₄
      simp only [normalForm.stepP.used_nonterminals'] at h₅
      exact h₅
    · split at h₃
    · split at h₃
    · split at h₃
  · rename_i h₃
    split at h₃
    · simp only [Sum.inr.injEq] at h₃
      simp only [h₃]
    · exfalso
      simp only [reduceCtorEq] at h₃
    · split at h₃
    · split at h₃
    · split at h₃

lemma normalForm_step_decomposition' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  (h : normalForm.stepP w (fun _ ↦ .zero)) :
    ∃ s : List α, w = s.map .terminal ++ [.nonterminal (.ender fun _ ↦ .zero)] := by
  have h₃ : w.take (w.length - 1) ++ [w.getLast h.nonempty] = w :=
    List.take_append_getLast w h.nonempty
  rw [h.last_is_ender] at h₃
  --
  let s : List α :=
    (w.take (w.length - 1)).pmap
      (P := fun x ↦ x ∈ (w.take (w.length - 1)))
      fun x hx ↦
        match x with
        | .terminal a => a
        | .nonterminal _ =>
          nomatch show False by
            rename_i n
            simp only at hx
            have h₁ : .nonterminal n ∈ w := List.mem_of_mem_take hx
            have h₂ := h.used_nonterminal _ h₁
            unfold normalForm.stepP.used_nonterminals' at h₂
            split at h₂
            · rename_i s b g
              subst g
              replace hx := List.mem_of_mem_take hx
              have h₂ := h.used_nonterminal'.mp hx
              simp only [reduceCtorEq] at h₂
            · rename_i s g
              subst g
              have h₂ := h.nodup_nonterminals (.ender fun _ ↦ .zero)
              rw [Nat.le_one_iff_eq_zero_or_eq_one] at h₂
              obtain h₂ | h₂ := h₂
              · rw [List.count_eq_zero] at h₂
                rw [← h₃] at h₂
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true,
                  not_true_eq_false] at h₂
              · rw [← h₃] at h₂
                simp only [List.count_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
                  List.nodup_nil, and_self, List.mem_cons, or_false, List.count_eq_one_of_mem,
                  Nat.add_eq_right] at h₂
                rw [List.count_eq_zero] at h₂
                exact h₂ hx
            · simp only [Bool.false_eq_true] at h₂
      (fun _ h ↦ h)
  use s
  rw [← h₃]
  simp only [List.append_cancel_right_eq]
  --
  subst s
  rw [List.map_pmap]
  --
  apply Eq.symm
  rw [List.pmap_eq_self]
  intro x hx
  split
  · rfl
  · split

lemma normalForm_step_decomposition_contains_single {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  {f}
  (h₀ : normalForm.stepP w f)
  {s : List (V ⊕ α)}
  (h₁ : w =
    (s.map fun x ↦
      match x with
      | .inl v => .nonterminal (.single v f)
      | .inr a => .terminal a)
    ++ [.nonterminal (.ender f)])
  {v f'}
  (h₂ : .nonterminal (.single v f') ∈ w) :
    ∃ i : Fin s.length, (s[i] = .inl v ∧ (∀ j : Fin s.length, j ≠ i → s[j] ≠ .inl v)) := by
  rw [h₁] at h₂
  simp only [List.mem_append, List.mem_map, Sum.exists, Symbol.nonterminal.injEq,
    Nonterminal.single.injEq, ↓existsAndEq, true_and, reduceCtorEq, and_false, exists_false,
    or_false, List.mem_cons, List.not_mem_nil, or_self] at h₂
  replace h₂ := h₂.left
  have ⟨i, hi⟩ : ∃ i : Fin s.length, s[i] = .inl v := List.mem_iff_get.mp h₂
  use i, hi
  by_contra contra
  simp only [ne_eq, Fin.getElem_fin, not_forall, Decidable.not_not] at contra
  obtain ⟨x, hx, contra⟩ := contra
  --
  have h₃ : s.take i ++ [s[i]] ++ s.drop (↑i + 1) = s := by
    simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
  --
  replace hi : s[i] = .inl v := hi
  rw [hi] at h₃
  rw [← h₃] at h₁
  clear h₃ hi
  --
  have h₄ := h₀.nodup_nonterminals (.single v f)
  rw [h₁] at h₄
  clear h₁
  --
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.map_append,
    List.map_cons, List.count_append, List.count_cons_self,
    not_false_eq_true, ne_eq, Symbol.nonterminal.injEq,
    reduceCtorEq, List.count_cons_of_ne, List.count_nil, add_zero] at h₄

  simp only [← Nat.add_assoc, add_le_iff_nonpos_left, nonpos_iff_eq_zero, Nat.add_eq_zero] at h₄
  -- --
  obtain ⟨h₄, h₅⟩ := h₄
  --
  rw [List.count_eq_zero] at h₄ h₅
  --
  by_cases h₆ : x < i
  · have h₇ : .inl v ∈ s.take i := by
      rw [← contra]
      have h₇ := (List.mem_take_iff_getElem (l := s) (i := i)).mpr
        ⟨↑x
        ,by simp only [Fin.is_le', inf_of_le_left, Fin.val_fin_lt, h₆]
        ,contra⟩
      rw [← contra] at h₇
      exact h₇
      --
    rw [List.mem_iff_getElem] at h₇
    obtain ⟨j, hj, h₇⟩ := h₇
    --
    have h₈ : (s.take i).take j ++ [(s.take i)[j]] ++ (s.take i).drop (j + 1) = s.take i := by
      simp only [List.take_append_getElem, List.take_append_drop]
    rw [← h₈] at h₄
    simp only [List.getElem_take, List.append_assoc, List.cons_append, List.nil_append,
      List.map_append, List.map_take, List.map_cons, List.map_drop, List.mem_append, List.mem_cons,
      not_or, ne_eq] at h₄
    replace h₄ := h₄.right.left
    have : j < s.length := by
      clear * - hj
      rw [List.length_take] at hj
      calc j
        _ < _ := hj
        _ ≤ s.length := Nat.min_le_right _ _
    have h₉ : (s.take i)[j] = s[j] := List.getElem_take
    rw [h₉] at h₇
    simp only [h₇, not_true_eq_false] at h₄
  · simp only [not_lt] at h₆
    by_cases h₇ : i < x
    · have h₈ : .inl v ∈ s.drop (i + 1) := by
        clear * - h₇ contra
        exact (List.mem_drop_iff_getElem (l := s) (i := i + 1) (a := .inl v)).mpr
          ⟨x - (i + 1)
          ,(by grind only [cases Or])
          ,(by grind only [cases Or])⟩
      replace ⟨j, hj, h₈⟩ := List.mem_iff_getElem.mp h₈
      --
      have h₉ :
          (s.drop (i + 1)).take j ++
          [(s.drop (i + 1))[j]] ++
          (s.drop (i + 1)).drop (j + 1) = s.drop (i + 1) := by
        simp only [List.take_append_getElem, List.take_append_drop]
      --
      rw [← h₉] at h₅
      simp only [List.getElem_drop, List.drop_drop, List.append_assoc, List.cons_append,
        List.nil_append, List.map_append, List.map_take, List.map_drop, List.map_cons,
        List.mem_append, List.mem_cons, not_or, ne_eq] at h₅
      replace h₅ := h₅.right.left
      --
      have _ : ↑i + 1 + j < s.length := by
        clear * - hj
        rw [List.length_drop] at hj
        exact Nat.add_lt_of_lt_sub' hj
      --
      have h₃ : s[↑i + 1 + j] = (List.drop (↑i + 1) s)[j] := by
        simp only [List.getElem_drop]
      rw [← h₃] at h₈
      simp only [h₈, not_true_eq_false] at h₅
    · clear * - hx h₆ h₇
      grind only

lemma normalForm_step_decomposition_contains_single' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  {f}
  (h₀ : normalForm.stepP w f)
  {s : List (V ⊕ α)}
  (h₁ : w =
    (s.map fun x ↦
      match x with
      | .inl v => .nonterminal (.single v f)
      | .inr a => .terminal a)
    ++ [.nonterminal (.ender f)])
  {v f'}
  (h₂ : .nonterminal (.single v f') ∈ w) :
    @List.count (V ⊕ α) instBEqOfDecidableEq (.inl v) s = 1 := by
  have h₃ := h₀.used_nonterminal _ h₂
  simp only [normalForm.stepP.used_nonterminals'] at h₃
  subst f'

  have ⟨n, hn, h₃⟩ := normalForm_step_decomposition_contains_single h₀ h₁ h₂

  have h₄ : s.take n ++ [s[n]] ++ s.drop (↑n + 1) = s := by
    simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
  rw [hn] at h₄

  rw [← h₄]
  simp only [List.count_append, List.count_singleton]
  clear h₁
  simp only [BEq.rfl, ↓reduceIte]

  rw [Nat.add_comm]
  simp only [← Nat.add_assoc, Nat.add_eq_right, Nat.add_eq_zero]
  simp only [List.count_eq_zero]
  constructor
  · intro contra
    rw [List.mem_iff_getElem] at contra
    obtain ⟨i, hi, contra⟩ := contra
    simp only [List.length_drop] at hi
    have h₄ := h₃
      ⟨n + 1 + i,
      (by
        clear * - hi
        grind only [cases Or])⟩
      (by
        clear * -
        grind only)
    clear * - h₄ contra
    simp_all only [List.getElem_drop, Fin.getElem_fin, ne_eq, not_true_eq_false]
  · intro contra
    rw [List.mem_iff_getElem] at contra
    obtain ⟨i, hi, contra⟩ := contra
    simp only [List.length_take, Fin.is_le', inf_of_le_left] at hi
    have h₄ := h₃
      ⟨i, by
        clear * - hi
        grind only⟩
      (by
        clear * - hi
        grind only)
    clear * - h₄ contra
    grind only [= List.length_take, = Fin.getElem_fin, = List.getElem_take]

lemma normalForm_step_decomposition_contains_single'' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  {f}
  (h₀ : normalForm.stepP w f)
  {s : List (V ⊕ α)}
  (h₁ : w =
    (s.map fun x ↦
      match x with
      | .inl v => .nonterminal (.single v f)
      | .inr a => .terminal a)
    ++ [.nonterminal (.ender f)])
  {v}
  (h₂ : .inl v ∈ s) :
    @List.count (V ⊕ α) instBEqOfDecidableEq (.inl v) s = 1 := by
  replace h₂ : .nonterminal (.single v f) ∈ w := by
    rw [h₁]
    simp only [List.mem_append, List.mem_map, Sum.exists, Symbol.nonterminal.injEq,
      Nonterminal.single.injEq, and_true, exists_eq_right, reduceCtorEq, and_false, exists_false,
      or_false, List.mem_cons, List.not_mem_nil, or_self]
    exact h₂
  exact normalForm_step_decomposition_contains_single' h₀ h₁ h₂

lemma normalForm_step_decomposition_contains_variable {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  {f}
  (h₁ : normalForm.stepP w f)
  {s : List (V ⊕ α)}
  (h₂ : w =
    (s.map fun x ↦
      match x with
      | .inl v => .nonterminal (.single v f)
      | .inr a => .terminal a)
    ++ [.nonterminal (.ender f)]) :
    ∀ v, .inl v ∈ s ↔ f v = .one := by
  intro v
  constructor
  · intro hv
    have ⟨n, h'⟩ := List.mem_iff_get.mp hv
    replace h' : s[n] = .inl v := h'
    have h'' : s.take n ++ [s[n]] ++ s.drop (↑n + 1) = s := by
      simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
    rw [h'] at h''
    rw [← h''] at h₂
    clear h' h''
    replace h₂ : .nonterminal (.single v f) ∈ w := by
      rw [h₂]
      simp only [
        List.append_assoc, List.cons_append, List.nil_append, List.map_append, List.map_take,
        List.map_cons, List.map_drop, List.mem_append, List.mem_cons, Symbol.nonterminal.injEq,
        reduceCtorEq, List.not_mem_nil, or_self, or_false, true_or, or_true]
    exact h₁.used_nonterminal'.mp h₂
  · intro hv
    replace hv := h₁.used_nonterminal'.mpr hv
    rw [h₂] at hv
    simp only [List.mem_append, List.mem_map, Sum.exists, Symbol.nonterminal.injEq,
      Nonterminal.single.injEq, and_true, exists_eq_right, reduceCtorEq, and_false, exists_false,
      or_false, List.mem_cons, List.not_mem_nil, or_self] at hv
    exact hv

lemma normalForm_start_rewrite_start {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  (h : normalForm.startP w) :
    E.LULTImpFiEDT0L.rewriteWord .start w
    = [.nonterminal (.single E.initial fun v ↦ if v = E.initial then .one else .zero),
      .nonterminal (.ender fun v ↦ if v = E.initial then .one else .zero) ] := by
  obtain rfl := h
  unfold LULTImpFiEDT0L rewriteWord
  simp only [rewriteSymbol, List.flatMap_cons, rewriteSymbol_nonterminal, List.flatMap_nil,
    List.append_nil]

lemma normalForm_start_rewrite_not_start {α V T : Type*}
  [finV : Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  {w : List (annotated_symbols E)}
  (h₁ : normalForm.startP w)
  {t : annotated_tables E}
  (h₂ : t ≠ .start) :
    E.LULTImpFiEDT0L.rewriteWord t w = [.nonterminal .dead] := by
  obtain rfl := h₁
  unfold LULTImpFiEDT0L rewriteWord
  simp only [rewriteSymbol, List.flatMap_cons, rewriteSymbol_nonterminal, List.flatMap_nil,
    List.append_nil]
  split
  · exfalso
    exact h₂ rfl
  · rfl
  · rfl

lemma normalForm_start_rewrite_start' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T) :
    normalForm.stepP (E:=E)
      [.nonterminal (.single E.initial fun v ↦ if v = E.initial then .one else .zero),
        .nonterminal (.ender fun v ↦ if v = E.initial then .one else .zero) ] 
      (fun v ↦ if v = E.initial then .one else .zero) := by
  change
    let w' := _
    let f := _
    normalForm.stepP w' f
  extract_lets w' f
  --
  have property : normalForm.stepP w' f := {
    nonempty := by
      unfold w'
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    used_nonterminal := by
      unfold w' f
      simp only [List.mem_cons, Symbol.nonterminal.injEq, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      constructor
      · unfold normalForm.stepP.used_nonterminals'
        split
        · rename_i g h
          simp only [Nonterminal.single.injEq] at h
          have ⟨_, h_r⟩ := h
          exact h_r
        · rename_i g h
          simp only [reduceCtorEq] at h
        · rfl
      · unfold normalForm.stepP.used_nonterminals'
        split
        · rename_i g h
          simp only [reduceCtorEq] at h
        · rename_i g h
          simp only [Nonterminal.ender.injEq] at h
          exact h
        · rfl
    used_nonterminal' := by
      unfold w' f
      intro x
      constructor
      · intro hx
        simp only [List.mem_cons, Symbol.nonterminal.injEq, Nonterminal.single.injEq, and_true,
          reduceCtorEq, List.not_mem_nil, or_self, or_false] at hx
        subst hx
        simp only [↓reduceIte]
      · simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not, List.mem_cons,
          Symbol.nonterminal.injEq, Nonterminal.single.injEq, and_true, List.not_mem_nil, or_self,
          or_false, imp_self]
    nodup_nonterminals := by
      intro n
      unfold w'
      change
        let x₁ := _
        let x₂ := _
        List.count _ [x₁, x₂] ≤ 1
      extract_lets x₁ x₂
      have h₀ : x₁ ≠ x₂ := by
        unfold x₁ x₂
        simp only [ne_eq, Symbol.nonterminal.injEq, reduceCtorEq, not_false_eq_true]
      if h₁ : .nonterminal n = x₁ then
        rw [h₁]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true,
          List.nodup_nil, and_self, or_false, List.count_eq_one_of_mem, le_refl, h₀]
      else if h₂ : .nonterminal n = x₂ then
        rw [h₂]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true,
          List.nodup_nil, and_self, or_false, or_true, List.count_eq_one_of_mem, le_refl, h₀]
      else
        rw [Nat.le_one_iff_eq_zero_or_eq_one]
        left
        rw [List.count_eq_zero]
        simp only [List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true, h₁, h₂]
    last_is_ender := by
      unfold w' f
      simp only [ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_cons,
        List.getLast_singleton]
    }
  exact property

lemma normalForm_start_rewrite_not_start' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T) :
    normalForm.deadP (E := E) [.nonterminal .dead] := by
  use []
  simp only [List.map_nil, List.nil_append]

@[simp]
lemma normalForm_dead_rewrite {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.deadP w) (t) :
    E.LULTImpFiEDT0L.rewriteWord t w = w := by
  obtain ⟨s, rfl⟩ := h
  simp only [rewriteWord_append, rewriteWord_terminals, rewriteWord_cons, rewriteSymbol_nonterminal,
    rewriteWord_nil, List.append_nil, List.append_cancel_left_eq]
  unfold LULTImpFiEDT0L
  simp only
  split <;> rfl

@[simp]
lemma normalForm_output_rewrite {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.outputP w) (t) :
    E.LULTImpFiEDT0L.rewriteWord t w = w := by
  obtain ⟨s, rfl⟩ := h
  simp only [rewriteWord_terminals]

lemma normalForm_step_rewrite_start {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) :
    normalForm.deadP (E.LULTImpFiEDT0L.rewriteWord .start w) := by
  obtain ⟨s, rfl⟩ := normalForm_step_decomposition h
  clear h
  --
  unfold normalForm.deadP
  simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
    List.append_nil]
  --
  conv =>
    arg 1
    intro s'
    lhs
    arg 2
    unfold LULTImpFiEDT0L
    simp only
  --
  simp only [List.append_cancel_right_eq]
  induction s with
  | nil =>
    simp only [List.map_nil, rewriteWord_nil, List.nil_eq, List.map_eq_nil_iff, exists_eq]
  | cons a as ih =>
    simp only [List.map_cons, rewriteWord_cons]
    obtain ⟨s'', ih⟩ := ih
    rw [ih]
    split
    · unfold LULTImpFiEDT0L
      simp only [rewriteSymbol, rewriteSymbol_nonterminal, List.nil_append, exists_apply_eq_apply']
    · rename_i a
      use a::s''
      simp only [rewriteSymbol_terminal, List.cons_append, List.nil_append, List.map_cons]

lemma normalForm_step_rewrite_final₁ {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E))
  (h : normalForm.stepP w fun _ ↦ .zero) :
    ∃ s : List α,
      w = s.map .terminal ++ [.nonterminal (.ender fun _ ↦ .zero)]
      ∧ E.LULTImpFiEDT0L.rewriteWord .final w = s.map .terminal := by
  have ⟨s, h₁⟩ := normalForm_step_decomposition' h
  use s, h₁
  rw [h₁]
  unfold LULTImpFiEDT0L
  simp only [rewriteSymbol, rewriteWord_append, rewriteWord_terminals, rewriteWord_cons,
    rewriteSymbol_nonterminal, ↓reduceIte, rewriteWord_nil, List.append_nil]

lemma normalForm_step_rewrite_final {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) {f}
  (h₁ : normalForm.stepP w f)
  (h₂ : f ≠ fun _ ↦ .zero) :
    normalForm.deadP (E.LULTImpFiEDT0L.rewriteWord .final w) := by
  have ⟨s, h₃⟩ := normalForm_step_decomposition h₁
  rw [h₃]
  simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
    List.append_nil]
  --
  conv =>
    arg 1
    rhs
    unfold LULTImpFiEDT0L
    simp only [↓reduceIte, h₂]
  --
  unfold normalForm.deadP
  simp only [List.append_cancel_right_eq]
  --
  clear h₃
  --
  induction s with
  | nil =>
    simp only [List.map_nil, rewriteWord_nil, List.nil_eq, List.map_eq_nil_iff, exists_eq]
  | cons a as ih =>
    obtain ⟨s, ih⟩ := ih
    simp only [List.map_cons, rewriteWord_cons]
    rw [ih]
    clear ih
    --
    split
    · use s
      unfold LULTImpFiEDT0L
      simp only [rewriteSymbol, rewriteSymbol_nonterminal, List.nil_append]
    · rename_i a
      use a::s
      simp only [rewriteSymbol_terminal, List.cons_append, List.nil_append, List.map_cons]

lemma normalForm_step_rewrite_step {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) {f}
  (h : normalForm.stepP w f) (g t) :
    if validReplacement f g t
    then normalForm.stepP (E.LULTImpFiEDT0L.rewriteWord (.step t g) w) g
    else normalForm.deadP (E.LULTImpFiEDT0L.rewriteWord (.step t g) w) := by
  split
  · rename_i h₁
    have ⟨s, h₃⟩ := normalForm_step_decomposition h
    --
    have sub :
      E.LULTImpFiEDT0L.rewriteWord (.step t g) w =
      E.LULTImpFiEDT0L.rewriteWord (.step t g) w := rfl
    --
    conv at sub => rhs ; rw [h₃]
    --
    simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
      List.append_nil] at sub
    --
    conv at sub =>
      rhs
      rhs
      unfold LULTImpFiEDT0L
      simp only [↓reduceIte, h₁]
    clear h₃
    --
    change
      let w' := _
      _ = (w' ++ _)
      at sub
    extract_lets w' at sub
    --
    have used_nonterminal' : ∀ {x : V},
        .nonterminal (.single x g) ∈ E.LULTImpFiEDT0L.rewriteWord (.step t g) w ↔ g x = .one := by
      intro x
      constructor
      · intro h₂
        replace ⟨y, hy, h₂⟩ := rewriteWord_nonterminal_mem.mp h₂
        --
        cases y
        · exfalso
          unfold LULTImpFiEDT0L at h₂
          simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
            or_self] at h₂
        · exfalso
          unfold LULTImpFiEDT0L at h₂
          simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
            or_self] at h₂
        · rename_i b f'
          have h₂ := h.used_nonterminal _ hy
          simp only [normalForm.stepP.used_nonterminals'] at h₂
          subst f'
          --
          have h₄ := h.used_nonterminal'.mp hy
          --
          simp only [LULTImpFiEDT0L, rewriteSymbol, h₁, ↓reduceIte, List.mem_flatMap] at h₂
          obtain ⟨a, h₂, h₃⟩ := h₂
          --
          split at h₃
          · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₃
          · split at h₃
            · rename_i x' x'' hx'
              simp only [List.mem_cons, Symbol.nonterminal.injEq, Nonterminal.single.injEq,
                and_true, List.not_mem_nil, or_false] at h₃
              subst x'
              exact hx'
            · simp only [List.not_mem_nil] at h₃
            · simp only [List.not_mem_nil] at h₃
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₃
        · exfalso
          unfold LULTImpFiEDT0L at h₂
          simp only at h₂
          split at h₂
           <;> simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
                  or_self] at h₂
      · intro h₂
        have h₃ := h₁.nodup_ensure_one _ h₂
        have ⟨y, hy, h₄⟩ := Finset.sum_pos_iff.mp (Nat.lt_of_sub_eq_succ h₃)
        replace h₄ : .nonterminal x ∈ E.tables t y := List.count_pos_iff.mp h₄
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have h₅ := h.used_nonterminal'.mpr hy
        --
        simp only [LULTImpFiEDT0L, rewriteSymbol, rewriteWord_nonterminal_mem, exists_prop]
        --
        use .single y f, h₅
        --
        simp only [↓reduceIte, List.mem_flatMap, h₁]
        --
        use .nonterminal x, h₄
        --
        simp only [List.mem_cons, List.not_mem_nil, or_false, h₂]
    --
    have prop : normalForm.stepP (E.LULTImpFiEDT0L.rewriteWord (.step t g) w) g := {
      nonempty := by
        rw [sub]
        simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true]
      used_nonterminal := by
        rw [sub]
        intro x hx
        subst w'
        simp only [List.mem_append, List.mem_cons, Symbol.nonterminal.injEq, List.not_mem_nil,
          or_false] at hx
        obtain hx | hx := hx
        · simp only [rewriteWord, List.mem_flatMap, List.mem_map, Sum.exists] at hx
          obtain ⟨a, ⟨a', h₂ | h₃ ⟩ | ⟨b, h₂, h₃⟩⟩ := hx
          · rename_i h₃ h₄
            subst a
            unfold LULTImpFiEDT0L at h₃
            simp only [rewriteSymbol, rewriteSymbol_nonterminal, ↓reduceIte, List.mem_flatMap,
              h₁] at h₃
            obtain ⟨a'', h₃⟩ := h₃
            split at h₃
            · replace ⟨_, h₃⟩ := h₃
              simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₃
            · replace ⟨_, h₃⟩ := h₃
              split at h₃
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, List.not_mem_nil,
                  or_false] at h₃
                rw [h₃]
                unfold normalForm.stepP.used_nonterminals'
                simp only
              · exfalso
                simp only [List.not_mem_nil] at h₃
              · exfalso
                simp only [List.not_mem_nil] at h₃
              · exfalso
                simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₃
          · rename_i h₄ h₅ h₆ h₇
            subst a
            unfold LULTImpFiEDT0L at h₄
            simp only [rewriteSymbol, rewriteSymbol_nonterminal, ↓reduceIte, List.mem_flatMap,
              h₁] at h₄
            obtain ⟨a'', ha'', h₄⟩ := h₄
            split at h₄
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₄
            · split at h₄
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, List.not_mem_nil,
                  or_false] at h₄
                subst x
                unfold normalForm.stepP.used_nonterminals'
                simp only
              · simp only [List.not_mem_nil] at h₄
              · simp only [List.not_mem_nil] at h₄
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at h₄
          · rename_i h₄
            subst a
            simp only [rewriteSymbol_terminal, List.mem_cons, reduceCtorEq, List.not_mem_nil,
              or_self] at h₄
        · subst x
          unfold normalForm.stepP.used_nonterminals' 
          simp only
      used_nonterminal' := used_nonterminal'
      nodup_nonterminals := by
        intro n
        cases n
        · rw [Nat.le_one_iff_eq_zero_or_eq_one]
          left
          rw [List.count_eq_zero]
          simp only [rewriteWord_nonterminal_mem, exists_prop, not_exists, not_and]
          intro x hx
          --
          replace hx := h.used_nonterminal _ hx
          simp only [normalForm.stepP.used_nonterminals', Bool.false_eq_true] at hx
          split at hx
          · rename_i g
            subst g
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, rewriteSymbol, List.mem_flatMap, not_exists, not_and, h₁]
            intro x' hx'
            split
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
            · split
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
                or_self, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
                not_false_eq_true]
          · rename_i g
            subst g
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq,
              List.not_mem_nil, or_self, not_false_eq_true, h₁]
          · exfalso
            exact hx
        -- the following is just copy and paste of the above
        · rw [Nat.le_one_iff_eq_zero_or_eq_one]
          left
          rw [List.count_eq_zero]
          simp only [rewriteWord_nonterminal_mem, exists_prop, not_exists, not_and]
          intro x hx
          --
          replace hx := h.used_nonterminal _ hx
          simp only [normalForm.stepP.used_nonterminals', Bool.false_eq_true] at hx
          split at hx
          · rename_i g
            subst g
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, rewriteSymbol, List.mem_flatMap, not_exists, not_and, h₁]
            intro x' hx'
            split
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
            · split
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
                or_self, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
                not_false_eq_true]
          · rename_i g
            subst g
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq,
              List.not_mem_nil, or_self, not_false_eq_true, h₁]
          · exfalso
            exact hx
        · rename_i b f'
          if h₂ : f' = g then
            subst f'
            if h₃ : .nonterminal (.single b g) ∈ E.LULTImpFiEDT0L.rewriteWord (.step t g) w then
              have h₃_backup := h₃
              have h₄ := used_nonterminal'.mp h₃
              replace h₄ := h₁.nodup_ensure_one _ h₄
              --
              have ⟨s, h₅⟩ := normalForm_step_decomposition h 
              rw [h₅]
              simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal,
                rewriteWord_nil, List.append_nil, List.count_append, ge_iff_le]
              --
              conv =>
                lhs; rhs; unfold LULTImpFiEDT0L
                simp only [↓reduceIte, not_false_eq_true, ne_eq, Symbol.nonterminal.injEq,
                  reduceCtorEq, List.count_cons_of_ne, List.count_nil, h₁]
              --
              simp only [add_zero]
              --
              unfold rewriteWord
              rw [List.flatMap_map, List.count_flatMap]
              rw [Finset.sum_list_map_count]

              let s' : Finset (V ⊕ α) := s.toFinset.filter fun x ↦ ∃ v, x = .inl v

              change
                let F : (V ⊕ α) → ℕ := _
                ∑ m ∈ _, F m ≤ _
              extract_lets F

              have h_1 := Finset.sum_inter_add_sum_diff s.toFinset s' F

              have h_2 : ∀ x ∈ s.toFinset \ s', F x = 0 := by
                intro x hx
                unfold s' at hx
                simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_filter, not_and,
                  not_exists] at hx
                replace hx := hx.right hx.left
                cases x
                · rename_i v
                  replace hx := hx v
                  simp only [not_true_eq_false] at hx
                · rename_i a
                  unfold F
                  simp only [Function.comp_apply, rewriteSymbol_terminal,
                    not_false_eq_true, ne_eq,
                    reduceCtorEq, List.count_cons_of_ne, List.count_nil, nsmul_zero]
              rw [Finset.sum_eq_zero_iff.mpr h_2] at h_1
              simp only [add_zero] at h_1
              rw [← h_1]

              clear h_1 h_2

              have h₃ := normalForm_step_decomposition_contains_variable h h₅

              clear * - h₄ h h₁ h₃ h₅ h₃_backup used_nonterminal'

              let set2 : Finset V := { x | f x = .one }

              have h₃ := Finset.sum_bij' (s := s.toFinset ∩ s') (t := set2) (f := F)
                (g := fun x ↦ List.count (Symbol.nonterminal b) (E.tables t x))
                (fun x hx ↦
                  match x with
                  | .inl v => v
                  | .inr _ =>
                    nomatch show False by
                      unfold s' at hx
                      simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_filter,
                        reduceCtorEq, exists_false, and_false] at hx)
                (fun x hx ↦ .inl x)
                (by
                  intro a ha
                  simp only
                  split
                  · rename_i h'
                    unfold s' at h'
                    simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_filter,
                      Sum.inl.injEq, exists_eq', and_true, and_self] at h'
                    unfold set2
                    replace h₃ := (h₃ _).mp h'
                    simp only [Finset.mem_filter, Finset.mem_univ, and_self, h₃]
                  · split)
                (by
                  unfold set2 s'
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
                    List.mem_toFinset, Sum.inl.injEq, exists_eq', and_true, and_self]
                  intro v hv
                  replace hv := (h₃ _).mpr hv
                  exact hv)
                (by
                  unfold s'
                  simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_filter, and_self_left,
                    forall_and_index, forall_exists_index, Sum.forall, Sum.inl.injEq, implies_true,
                    reduceCtorEq, imp_self, and_self])
                (by
                  unfold set2
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, implies_true])
                (by
                  intro x hx
                  unfold s' at hx
                  simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_filter,
                    and_self_left] at hx
                  simp only
                  obtain ⟨h', v, rfl⟩ := hx

                  have hh := normalForm_step_decomposition_contains_single'' h h₅ h'

                  split
                  · unfold F
                    rw [hh]
                    simp only [Function.comp_apply, rewriteSymbol_nonterminal, smul_eq_mul, one_mul]
                    rename_i v_0 h_0 h_1 h_2
                    simp only [Sum.inl.injEq] at h_1
                    subst v_0
                    --
                    have h_g_of_b : g b = .one := used_nonterminal'.mp h₃_backup
                    --
                    unfold LULTImpFiEDT0L
                    simp only [↓reduceIte, rewriteSymbol, h₁]
                    clear * - h_g_of_b
                    change
                      let l := _
                      List.count _ (List.flatMap _ l) = List.count _ l
                    extract_lets l
                    --
                    induction l with
                    | nil =>
                      simp only [List.flatMap_nil, List.count_nil]
                    | cons a as ih =>
                      simp only [List.flatMap_cons, List.count_cons, List.count_append]
                      rw [ih, Nat.add_comm]
                      simp only [beq_iff_eq, Nat.add_left_cancel_iff]
                      --
                      split
                      · simp only [not_false_eq_true, ne_eq, reduceCtorEq, List.count_cons_of_ne,
                          List.count_nil, ↓reduceIte]
                      · simp only [Symbol.nonterminal.injEq]
                        rename_i x xv
                        by_cases h_case : xv = b
                        · subst xv
                          simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true,
                            List.nodup_nil, and_self, List.mem_cons, or_false,
                            List.count_eq_one_of_mem, ↓reduceIte, h_g_of_b]
                        · simp only [↓reduceIte, h_case]
                          split
                          · simp only [not_false_eq_true, ne_eq, Symbol.nonterminal.injEq,
                              Nonterminal.single.injEq, and_true, List.count_cons_of_ne,
                              List.count_nil, h_case]
                          · simp only [List.count_nil]
                          · simp only [List.count_nil]
                          · simp only [not_false_eq_true, ne_eq, reduceCtorEq,
                              List.count_cons_of_ne, List.count_nil]
                  · split)
              rw [h₃]
              unfold set2
              exact Nat.le_of_eq h₄
            else
              rw [Nat.le_one_iff_eq_zero_or_eq_one]
              left
              rw [List.count_eq_zero]
              exact h₃
          else
            rw [Nat.le_one_iff_eq_zero_or_eq_one]
            left
            rw [List.count_eq_zero]
            rw [sub]
            unfold w'
            unfold LULTImpFiEDT0L
            simp only [rewriteSymbol, List.mem_append, rewriteWord_nonterminal_mem, List.mem_map,
              Sum.exists, Symbol.nonterminal.injEq, reduceCtorEq, and_false, exists_false, or_false,
              exists_prop, exists_exists_and_eq_and, ↓reduceIte, List.mem_flatMap, List.mem_cons,
              List.not_mem_nil, or_self, not_exists, not_and, h₁]
            intro x hx x' hx'
            split
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
            · split
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, Nonterminal.single.injEq,
                  and_false, List.not_mem_nil, or_self, not_false_eq_true, h₂]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
                not_false_eq_true]
        · rename_i f'
          rw [sub]
          if h₂ : f' = g then
            rw [Nat.le_one_iff_eq_zero_or_eq_one]
            right
            subst f'
            simp only [List.count_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
              List.nodup_nil, and_self, List.mem_cons, or_false, List.count_eq_one_of_mem,
              Nat.add_eq_right]
            rw [List.count_eq_zero]
            unfold w'
            simp only [rewriteWord_nonterminal_mem, List.mem_map, Sum.exists,
              Symbol.nonterminal.injEq, reduceCtorEq, and_false, exists_false, or_false,
              exists_prop, exists_exists_and_eq_and, not_exists, not_and]
            intro x hx
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, rewriteSymbol, List.mem_flatMap, not_exists, not_and, h₁]
            intro x' hx'
            -- this is a copy of earlier
            split
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
            · split
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
                or_self, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
                not_false_eq_true]
          else
            rw [Nat.le_one_iff_eq_zero_or_eq_one]
            left
            rw [List.count_eq_zero]
            unfold w'
            simp only [List.mem_append, rewriteWord_nonterminal_mem, List.mem_map, Sum.exists,
              Symbol.nonterminal.injEq, reduceCtorEq, and_false, exists_false, or_false,
              exists_prop, exists_exists_and_eq_and, List.mem_cons, Nonterminal.ender.injEq,
              List.not_mem_nil, or_self, not_exists, not_and, h₂]
            intro x hx
            unfold LULTImpFiEDT0L
            simp only [↓reduceIte, rewriteSymbol, List.mem_flatMap, not_exists, not_and, h₁]
            intro x' hx'
            -- this is a copy of earlier
            split
            · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]
            · split
              · simp only [List.mem_cons, Symbol.nonterminal.injEq, reduceCtorEq, List.not_mem_nil,
                or_self, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.not_mem_nil, not_false_eq_true]
              · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self,
                not_false_eq_true]
      last_is_ender := by
        simp only [sub, ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_append_of_ne_nil,
          List.getLast_singleton]
      }
    exact prop
  · rename_i h₁
    have ⟨s, h₃⟩ := normalForm_step_decomposition h
    rw [h₃]
    simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
      List.append_nil]
    --
    conv =>
      arg 1
      rhs
      unfold LULTImpFiEDT0L
      simp only [↓reduceIte, h₁]
    --
    unfold normalForm.deadP
    simp only [List.append_cancel_right_eq]
    --
    clear h₃
    induction s with
    | nil =>
      simp only [List.map_nil, rewriteWord_nil, List.nil_eq, List.map_eq_nil_iff, exists_eq]
    | cons a as ih =>
      replace ⟨s, ih⟩ := ih
      simp only [List.map_cons, rewriteWord_cons]
      rw [ih]
      split
      · use s
        unfold LULTImpFiEDT0L
        simp only [rewriteSymbol, rewriteSymbol_nonterminal, ↓reduceIte, List.nil_append, h₁]
      · rename_i a
        use a::s
        simp only [rewriteSymbol_terminal, List.cons_append, List.nil_append, List.map_cons]

lemma normalForm_rewrite {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) {t}
  (h : normalForm w) :
    normalForm (E.LULTImpFiEDT0L.rewriteWord t w) := by
  cases h
  · rename_i h
    by_cases h₁ : t = .start
    · subst t
      have h₁ := normalForm_start_rewrite_start h
      have h₂ := normalForm_start_rewrite_start' E
      rw [← h₁] at h₂
      exact .step ⟨_, h₂⟩
    · have h₂ := normalForm_start_rewrite_not_start h h₁
      have h₃ := normalForm_start_rewrite_not_start' E
      rw [← h₂] at h₃
      exact .dead h₃
  · rename_i h
    have h₁ := normalForm_dead_rewrite w h t
    rw [h₁]
    exact .dead h
  · rename_i h
    have h₁ := normalForm_output_rewrite w h t
    rw [h₁]
    exact .output h
  · rename_i h
    replace ⟨f, h⟩ := h
    cases t
    · have h₁ := normalForm_step_rewrite_start w h
      exact .dead h₁
    · by_cases h₂ : f = fun _ ↦ .zero
      · subst f
        have ⟨s, hs, h₃⟩ := normalForm_step_rewrite_final₁ w h
        have h₄ : normalForm.outputP (E.LULTImpFiEDT0L.rewriteWord .final w) :=
          ⟨s, by subst w; exact h₃⟩
        exact .output h₄
      · have h₃ := normalForm_step_rewrite_final w h h₂
        exact .dead h₃
    · rename_i t g
      have h₁ := normalForm_step_rewrite_step w h g t
      split at h₁
      · exact .step ⟨_, h₁⟩
      · exact .dead h₁
  
lemma generates_normalForm {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T)
  (w : List (annotated_symbols E))
  (h : E.LULTImpFiEDT0L.generates w) :
    normalForm w := by
  induction h with
  | refl =>
    exact normalForm.start rfl
  | tail a as ih =>
    rename_i b c
    obtain ⟨τ, rfl⟩ := as
    exact normalForm_rewrite b ih

lemma finite_index {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T) :
    E.LULTImpFiEDT0L.IsIndex ((Fintype.card V) + 1) := by
  unfold IsIndex
  intro w h
  replace h := generates_normalForm E w h
  exact normalForm_count w h

def mapByStatusFun {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E) : Symbol α V → Option (Symbol α V)
| .terminal t => .some (.terminal t)
| .nonterminal v =>
  match f v with
  | .many .epsilon => .none
  | .many (.letter a) => .some (.terminal a)
        | _ => .some (.nonterminal v)

def mapByStatus {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (w : List (Symbol α V)) : List (Symbol α V) :=
    w.filterMap (mapByStatusFun f)

@[simp]
lemma mapByStatus_nil {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E) :
    mapByStatus f [] = [] := rfl

@[simp]
lemma mapByStatus_terminals {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E) (s : List α) :
    mapByStatus f (s.map .terminal) = s.map .terminal := by
  unfold mapByStatus mapByStatusFun
  induction s with
  | nil =>
    simp only [List.map_nil, List.filterMap_nil]
  | cons a as ih =>
    simp only [List.map_cons, Option.some.injEq, List.filterMap_cons_some, ih]

@[simp]
lemma mapByStatus_append {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (a b) :
    mapByStatus f (a ++ b) = mapByStatus f a ++ mapByStatus f b := by
  unfold mapByStatus
  simp only [List.filterMap_append]

@[simp]
lemma mapByStatus_zero {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} (a) :
    mapByStatus (E := E) (fun _ ↦ .zero) a = a := by
  induction a with
  | nil =>
    simp only [mapByStatus_nil]
  | cons a as ih =>
    rw [← List.singleton_append, mapByStatus_append, ih]
    unfold mapByStatus mapByStatusFun
    simp only [List.cons_append, List.nil_append]
    cases a
    · simp only [Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, List.cons_append,
        List.nil_append]
    · simp only [Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, List.cons_append,
      List.nil_append]

def deannotateWordFun {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} : annotated_symbols E → Option (Symbol α V)
| .terminal a => .some (.terminal a)
| .nonterminal (.single v _) => .some (.nonterminal v)
| _ => .none

def deannotateWord {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w : List (annotated_symbols E)) : List (Symbol α V) :=
    w.filterMap deannotateWordFun 

@[simp]
lemma deannotateWord_nil {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} :
    deannotateWord (E := E) [] = [] := rfl

@[simp]
lemma deannotateWord_ender {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} {f} :
    deannotateWord (E := E) [.nonterminal (.ender f)] = [] := rfl

@[simp]
lemma deannotateWord_append {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} {a b} :
    deannotateWord (E := E) (a ++ b) = deannotateWord a ++ deannotateWord b := by
  unfold deannotateWord
  simp only [List.filterMap_append]

lemma deannotateWord_cons {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} {a as} :
    deannotateWord (E := E) (a :: as) = deannotateWord [a] ++ deannotateWord as := by
  rw [← List.singleton_append, deannotateWord_append]

@[simp]
lemma deannotateWordFun_terminal {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} {a} :
    deannotateWordFun (E := E) (.terminal a) = .some (.terminal a) := rfl

@[simp]
lemma deannotateWord_terminals {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T} {s : List α} :
    deannotateWord (E := E) (s.map .terminal) = s.map .terminal := by
  induction s with
  | nil =>
    simp only [List.map_nil, deannotateWord_nil]
  | cons a as ih =>
    simp only [List.map_cons]
    rw [deannotateWord_cons, ih]
    rw [deannotateWord]
    simp only [deannotateWordFun_terminal, Option.some.injEq, List.filterMap_cons_some,
      List.filterMap_nil, List.cons_append, List.nil_append]

def annotateWordFun {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E) : (Symbol α V) → annotated_symbols E
| .terminal a => .terminal a
| .nonterminal v => .nonterminal (.single v f)

def annotateWord {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (w : List (Symbol α V)) : List (annotated_symbols E) :=
    (w.map (annotateWordFun f)) ++ [.nonterminal (.ender f)]

lemma rewrite_agrees {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (w_edt0l : List (Symbol α V))
  (w_lult : List (annotated_symbols E))
  {f}
  (h₁ : normalForm.stepP w_lult f)
  {g t}
  (h₂ : validReplacement f g t)
  (h₃ : mapByStatus f w_edt0l = deannotateWord w_lult) :
    mapByStatus g (E.rewriteWord t w_edt0l) =
    deannotateWord (E.LULTImpFiEDT0L.rewriteWord (.step t g) w_lult) := by
  obtain ⟨s, h₄⟩ := normalForm_step_decomposition h₁
  change
    let s_fun : V ⊕ α → annotated_symbols E := _
    _ = (List.map s_fun s) ++ _
    at h₄
  extract_lets s_fun at h₄
  subst w_lult
  --
  simp only [deannotateWord_append, deannotateWord_ender, List.append_nil] at h₃
  simp only [rewriteWord_append, rewriteWord_cons, rewriteSymbol_nonterminal, rewriteWord_nil,
    List.append_nil, deannotateWord_append]
  conv => rhs; rhs; unfold LULTImpFiEDT0L
  simp only [↓reduceIte, deannotateWord_ender, List.append_nil, h₂]
  --
  unfold mapByStatus deannotateWord at h₃

  let rec main_proof
    (w_edt0l : List (Symbol α V))
    (s' : List (V ⊕ α))
    (h' : s' <:+: s)
    (h :
      w_edt0l.filterMap (mapByStatusFun f) =
      List.filterMap deannotateWordFun (s'.map s_fun)) :
    --
    mapByStatus g (E.rewriteWord t w_edt0l) =
      List.filterMap deannotateWordFun 
        (E.LULTImpFiEDT0L.rewriteWord (.step t g) (s'.map s_fun)) := by
    match h_w : w_edt0l, h_s : s' with
    | .nil, .nil =>
      simp only [rewriteWord_nil, mapByStatus_nil, List.map_nil, List.filterMap_nil]
    | a::as, .nil =>
      rw [← List.singleton_append, List.filterMap_append] at h
      --
      have rhs : List.filterMap deannotateWordFun (List.map s_fun []) = [] := by
        simp only [List.map_nil, List.filterMap_nil]
      rw [rhs] at h
      --
      rw [List.append_eq_nil_iff] at h
      --
      have ⟨h_l, h_r⟩ := h
      conv at h_r => rhs; rw [← rhs]
      have R := main_proof as .nil h' h_r
      simp only [List.map_nil, rewriteWord_nil, List.filterMap_nil] at R
      --
      rw [← List.singleton_append, rewriteWord_append, mapByStatus_append]
      rw [R]
      simp only [rewriteWord_cons, rewriteWord_nil, List.append_nil, List.map_nil,
        List.filterMap_nil]
      --
      clear R h_r rhs h_s h
      simp only [List.filterMap_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq] at h_l
      --
      unfold mapByStatus
      simp only [List.filterMap_eq_nil_iff]
      --
      intro a' ha'
      --
      cases a
      · unfold mapByStatusFun at h_l
        simp only [reduceCtorEq] at h_l
      · rename_i v
        unfold mapByStatusFun at h_l
        unfold mapByStatusFun
        --
        have h₄ : f v = .many (.epsilon) := by
          split at h_l
          · simp only [reduceCtorEq] at h_l
          · split at h_l <;> simp only [reduceCtorEq] at h_l
            rename_i h1 h2 h3
            simp only [Symbol.nonterminal.injEq] at h1
            subst h1
            exact h3
        --
        have h₅ := h₂.valid_composition
        have h₆ := h₂.expansions_match
        --
        unfold
          status_all_nonterminals.range_at_table
          status_all_nonterminals.domain
          at h₅
        simp only at h₅
        rw [Finset.subset_iff] at h₅
        simp only [ne_eq, Finset.mem_sup, Finset.mem_filter, Finset.mem_univ, true_and,
          forall_exists_index, and_imp] at h₅
        --
        unfold EDT0LGrammar.rewriteSymbol at ha'
        simp only at ha'
        --
        cases a'
        · exfalso
          replace h₆ := h₆ v
          unfold validReplacement.expressions_match' at h₆
          simp only [List.flatMap_eq_nil_iff, h₄] at h₆
          replace h₆ := h₆ _ ha'
          simp only [List.cons_ne_self] at h₆
        --
        rename_i v
        replace h₅ := h₅ _
          (by simp only [reduceCtorEq, not_false_eq_true, h₄])
          (by simp only [reduceCtorEq, not_false_eq_true, h₄])
          ha'
        obtain ⟨left, right⟩ := h₅
        --
        simp only
        --
        rename_i v'
        --
        cases h₇ : g v
        · exfalso
          exact right h₇
        · exfalso
          exact left h₇
        · rename_i h₇'
          cases h₇'
          · simp only
          · replace h₆ := h₆ v'
            unfold validReplacement.expressions_match' at h₆
            simp only [List.flatMap_eq_nil_iff, h₄] at h₆
            replace h₆ := h₆ _ ha'
            simp only [List.cons_ne_self, h₇] at h₆
    | .nil, b::bs =>
      exfalso
      change [] = _ at h
      rw [← List.singleton_append, List.map_append, List.filterMap_append] at h
      replace h := h.symm
      rw [List.append_eq_nil_iff] at h
      replace h := h.left
      --
      unfold deannotateWord s_fun at h
      simp only [List.map_cons, List.map_nil, List.filterMap_eq_nil_iff, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq] at h
      split at h
      · unfold deannotateWordFun at h
        simp only [reduceCtorEq] at h
      · unfold deannotateWordFun at h
        simp only [reduceCtorEq] at h
    | a::as, b::bs =>
      have h_stepP := h₁ -- save it for later
      --
      cases h₄ : mapByStatusFun f a
      · conv at h =>
          lhs
          rw [← List.singleton_append, List.filterMap_append]
          simp only [List.filterMap_cons_none, List.filterMap_nil, List.nil_append, h₄]
        --
        have R := main_proof as (b::bs) h' h
        conv =>
          args
          · rw [← List.singleton_append, rewriteWord_append, mapByStatus_append]
          · rw [← List.singleton_append, List.map_append, rewriteWord_append, List.filterMap_append]
        rw [R]
        simp only [rewriteWord_cons, rewriteWord_nil, List.append_nil, List.map_cons,
          List.filterMap_append, List.map_nil, List.append_left_eq_self]
        clear R
        --
        unfold mapByStatusFun at h₄
        split at h₄
        · simp only [reduceCtorEq] at h₄
        --
        rename_i v'
        --
        have h₅ : f v' = .many .epsilon := by
          split at h₄ <;> simp only [reduceCtorEq] at h₄
          rename_i hh
          exact hh
        --
        have h₆ := h₂.expansions_match v'
        unfold validReplacement.expressions_match' at h₆
        simp only [h₅, List.flatMap_eq_nil_iff] at h₆
        --
        unfold mapByStatus
        unfold mapByStatusFun
        simp only [rewriteSymbol_nonterminal, List.filterMap_eq_nil_iff]
        --
        intro x' hx'
        split
        · replace h₆ := h₆ _ hx'
          simp only [List.cons_ne_self] at h₆
        · rename_i v''
          --
          have h_v := h₂.valid_composition
          unfold
            status_all_nonterminals.range_at_table
            status_all_nonterminals.domain
            at h_v
          simp only at h_v
          rw [Finset.subset_iff] at h_v
          simp only [ne_eq, Finset.mem_sup, Finset.mem_filter, Finset.mem_univ, true_and,
            forall_exists_index, and_imp] at h_v
          --
          replace h_v := h_v _
            (by simp only [reduceCtorEq, not_false_eq_true, h₅])
            (by simp only [reduceCtorEq, not_false_eq_true, h₅])
            hx'
          --
          obtain ⟨left, right⟩ := h_v
          --
          cases h₇ : g v''
          · exfalso
            exact right h₇
          · exfalso
            exact left h₇
          · rename_i ww
            cases ww
            · simp only
            · exfalso
              replace h₆ := h₆ _ hx'
              simp only [List.cons_ne_self, h₇] at h₆
      --
      cases h₅ : deannotateWordFun (s_fun b)
      · conv at h =>
          rhs
          rw [← List.singleton_append, List.map_append, List.filterMap_append]
          simp only [List.map_cons, List.map_nil, h₅, List.filterMap_cons_none,
            List.filterMap_nil, List.nil_append]
        --
        have R := main_proof (a::as) bs (by
          calc bs
            _ <:+: b::bs := List.infix_cons (List.infix_refl bs)
            _ <:+: s := h') h
        --
        conv =>
          rhs
          rw [← List.singleton_append, List.map_append, rewriteWord_append, List.filterMap_append]
          simp only [List.map_cons, List.map_nil, rewriteWord_cons, rewriteWord_nil,
            List.append_nil]
        --
        rw [R]
        simp only [List.self_eq_append_left, List.filterMap_eq_nil_iff]
        --
        intro x' hx'
        --
        unfold s_fun at h₅
        split at h₅
        · unfold deannotateWordFun at h₅
          simp only [reduceCtorEq] at h₅
        · unfold deannotateWordFun at h₅
          simp only [reduceCtorEq] at h₅
      -----------
      conv at h =>
        args
        · rw [← List.singleton_append, List.filterMap_append]
          lhs
          simp only [Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, h₄]
        · rw [← List.singleton_append, List.map_append, List.filterMap_append]
          lhs
          simp only [List.map_cons, List.map_nil, Option.some.injEq,
            List.filterMap_cons_some, List.filterMap_nil, h₅]
      --
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      --
      have R := main_proof as bs (by
          calc bs
            _ <:+: b::bs := List.infix_cons (List.infix_refl bs)
            _ <:+: s := h') h
      --
      conv =>
        args
        · rw [← List.singleton_append, rewriteWord_append, mapByStatus_append]
        · rw [← List.singleton_append, List.map_append, rewriteWord_append]
      rw [R]
      clear R h
      simp only [rewriteWord_cons, rewriteWord_nil, List.append_nil, List.map_cons, List.map_nil,
        List.filterMap_append, List.append_cancel_right_eq]
      rename_i x''

      clear h_s h_w w_edt0l h₃ h₁

      cases a
      · rename_i a''
        unfold mapByStatusFun at h₄
        simp only [Option.some.injEq] at h₄
        subst h₄
        unfold deannotateWordFun at h₅
        split at h₅
        · simp only [Option.some.injEq, Symbol.terminal.injEq] at h₅
          rename_i heq
          subst h₅
          rw [heq]
          clear heq
          unfold mapByStatus mapByStatusFun deannotateWordFun
          simp only [rewriteSymbol_terminal, Option.some.injEq, List.filterMap_cons_some,
            List.filterMap_nil]
        · simp only [Option.some.injEq, reduceCtorEq] at h₅
        · simp only [reduceCtorEq] at h₅

      rw [← h₄] at h₅
      clear h₄
      cases b
      · rename_i n val
        unfold s_fun at h₅
        simp only at h₅
        unfold deannotateWordFun at h₅
        simp only at h₅
        --
        unfold mapByStatusFun at h₅
        simp only at h₅
        --
        cases h'' : f n 
        rotate_right
        · rename_i ww
          cases ww <;> simp only [Option.some.injEq, reduceCtorEq, h''] at h₅
        --
        · simp only [Option.some.injEq, Symbol.nonterminal.injEq, h''] at h₅
          subst h₅
          
          have h₁ : .inl val ∈ s := by
            clear * - h'
            rw [← List.singleton_append] at h'
            have h₁ : (.inl val : V ⊕ α) ∈ [.inl val] := List.mem_singleton.mpr rfl
            have h₂ : [(.inl val : V ⊕ α)] <:+: [.inl val] ++ bs := List.infix_append_left
            have h₃ : (.inl val : V ⊕ α) ∈ [.inl val] ++ bs :=
              List.mem_append_left bs h₁
            exact List.IsInfix.mem h₃ h'
          replace h₁ : f val = .one :=
            (normalForm_step_decomposition_contains_variable h_stepP rfl val).mp h₁
          
          rw [h₁] at h''
          simp only [reduceCtorEq] at h''
        · simp only [Option.some.injEq, Symbol.nonterminal.injEq, h''] at h₅
          subst h₅
          --
          have h₁ : .inl val ∈ s := by
            clear * - h'
            rw [← List.singleton_append] at h'
            have h₁ : (.inl val : V ⊕ α) ∈ [.inl val] := List.mem_singleton.mpr rfl
            have h₂ : [(.inl val : V ⊕ α)] <:+: [.inl val] ++ bs := List.infix_append_left
            have h₃ : (.inl val : V ⊕ α) ∈ [.inl val] ++ bs :=
              List.mem_append_left bs h₁
            exact List.IsInfix.mem h₃ h'
          replace h₁ : f val = .one :=
            (normalForm_step_decomposition_contains_variable h_stepP rfl val).mp h₁
          
          unfold s_fun
          simp only

          unfold EDT0LGrammar.rewriteSymbol
          simp only

          unfold mapByStatus mapByStatusFun deannotateWordFun LULTImpFiEDT0L
          simp only [↓reduceIte, rewriteSymbol, h₂]
          --
          rw [List.filterMap_flatMap, List.filterMap_eq_flatMap_toList]
          --
          change
            let p : _ → _ := _
            let q : _ → _ := _
            List.flatMap p _ = List.flatMap q _
          extract_lets p q
          --
          have h₉ : ∀ x ∈ E.tables t val, p x = q x := by
            subst p q
            intro x hx
            simp only
            cases x
            · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
                List.filterMap_nil]
            · rename_i n
              simp only
              cases h''' : g n
              · exfalso
                exact h₂.nodup_ensure_zero _ h''' _ h'' hx
              · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
                  List.filterMap_nil]
              · rename_i ww
                cases ww
                · simp only [Option.toList_none, List.filterMap_nil]
                · simp only [Option.toList_some, Option.some.injEq, List.filterMap_cons_some,
                    List.filterMap_nil]
          rw [List.flatMap_congr h₉]
      · unfold deannotateWordFun mapByStatusFun s_fun at h₅
        simp only at h₅
        split at h₅
        · simp only [reduceCtorEq] at h₅
        · simp only [Option.some.injEq, Symbol.terminal.injEq] at h₅
          subst h₅
          rename_i v'' _ _ heq
          have h₃ := h₂.expansions_match v''
          unfold validReplacement.expressions_match' at h₃
          simp only [heq, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_nil,
            List.append_nil] at h₃
          unfold EDT0LGrammar.rewriteSymbol
          simp only
          --
          unfold mapByStatus mapByStatusFun deannotateWordFun s_fun
          simp only [Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil]
          --
          have h₄ := h₂.valid_composition
          unfold
            status_all_nonterminals.range_at_table
            status_all_nonterminals.domain
            at h₄
          rw [Finset.subset_iff] at h₄
          simp only [ne_eq, Finset.mem_sup, Finset.mem_filter, Finset.mem_univ, true_and,
            forall_exists_index, and_imp] at h₄
          
          have h₅ : ∀ x (_ : .nonterminal x ∈ E.tables t v''), g x ≠ .one ∧ g x ≠ .zero := by
            intro x hx
            replace h₄ := h₄ _
              (by simp only [reduceCtorEq, not_false_eq_true, heq])
              (by simp only [reduceCtorEq, not_false_eq_true, heq])
              hx
            exact h₄
          rw [List.filterMap_eq_flatMap_toList]
          --
          rename_i a'''
          
          replace h₃ := congr_arg (β := List (Symbol α V)) (fun l ↦ l.map .terminal) h₃
          simp only at h₃
          rw [List.map_flatMap, List.map_singleton] at h₃

          change
            let p : _ → _ := _
            List.flatMap p _ = _
            at h₃
          extract_lets p at h₃
          --
          change
            let q : _ → _ := _
            List.flatMap q _ = _
          extract_lets q

          have h₆ : ∀ x ∈ E.tables t v'', p x = q x := by
            intro x hx
            unfold p q
            cases x
            · simp only [List.map_cons, List.map_nil, Option.toList_some]
            · rename_i n
              have ⟨left, right⟩ := h₅ _ hx
              simp only
              cases hh : g n
              · exfalso
                exact right hh
              · exfalso
                exact left hh
              · rename_i ww
                cases ww
                · simp only [List.map_nil, Option.toList_none]
                · simp only [List.map_cons, List.map_nil, Option.toList_some]

          rw [List.flatMap_congr h₆] at h₃
          exact h₃
        · simp only [Option.some.injEq, reduceCtorEq] at h₅
  exact main_proof w_edt0l s (List.infix_refl s) h₃

end LULTImpFiEDT0L
end EDT0LGrammar

