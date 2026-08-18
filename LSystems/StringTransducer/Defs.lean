/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import Mathlib.Computability.Language

import Mathlib.Data.Fintype.Prod

@[expose] public section

@[ext]
structure StringTransducer (α β σ : Type*) where
  start : σ
  accept : Set σ
  step : σ → α → (σ × List β)
  final : (q : σ) → (h : q ∈ accept) → List β

def StringTransducer.mk' {α β σ}
  (start : σ)
  (accept' : Finset σ)
  (step : σ → α → (σ × List β))
  (final' : (q : σ) → (h : q ∈ accept') → List β) : StringTransducer α β σ :=
  ⟨start, accept', step, final'⟩

instance {α β σ} [DecidableEq σ] {start accept' step final'} :
    DecidablePred (· ∈ (@StringTransducer.mk' α β σ start accept' step final').accept) := by
  unfold StringTransducer.mk'
  exact inferInstance

namespace StringTransducer
variable {α β σ} (S : StringTransducer α β σ)

@[simp]
def rewriteWithoutFinal : σ → List α → σ × List β
  | q, [] => (q, [])
  | q, a :: as =>
    let ⟨q_next, head⟩ := S.step q a;
    let ⟨q_last, tail⟩ := rewriteWithoutFinal q_next as;
    (q_last, head ++ tail)

@[simp]
lemma rewriteWithoutFinal_append (q : σ) (u v : List α) :
    S.rewriteWithoutFinal q (u ++ v) =
      let ⟨q',u'⟩ := S.rewriteWithoutFinal q u
      let ⟨q'',v'⟩ := S.rewriteWithoutFinal q' v
      (q'', u' ++ v') := by
  split
  rename_i x q_last tail hq
  split
  rename_i x' q_last' tail' hq'
  induction u generalizing q tail with
  | nil =>
    simp only [List.nil_append]
    simp only [rewriteWithoutFinal, Prod.mk.injEq, List.nil_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    simpa using hq'
  | cons x xs ih =>
    simp only [List.cons_append, rewriteWithoutFinal, Prod.mk.injEq]
    simp only [rewriteWithoutFinal, Prod.mk.injEq] at hq
    replace ih := ih (S.3 q x).1 (S.rewriteWithoutFinal (S.3 q x).1 xs).2 (by
      obtain ⟨rfl, _ ⟩ := hq
      rfl)
    grind only

def rewrite [DecidablePred (· ∈ S.accept)] (source : List α) : Option (List β) :=
  let ⟨q,w⟩ := S.rewriteWithoutFinal S.start source
  if h : q ∈ S.accept then w ++ S.final q h else .none

def Rewrites (source : List α) (target : List β) : Prop :=
  let ⟨q,w⟩ := S.rewriteWithoutFinal S.start source
  ∃ h : q ∈ S.accept, target = w ++ S.final q h

lemma rewrite_eq_Rewrites [DecidablePred (· ∈ S.accept)] (source : List α) (target : List β) :
    S.Rewrites source target ↔ S.rewrite source = target := by
  simp only [Rewrites, rewrite, Option.dite_none_right_eq_some, Option.some.injEq]
  tauto

def map (L : Language α) : Language β := { w : List β | ∃ u ∈ L, S.Rewrites u w}

end StringTransducer

def Function.IsStringTransduction {α β} (f : Language α → Language β) : Prop :=
  ∃ (n : ℕ), ∃ (S : StringTransducer α β (Fin n)), ∀ (L : Language α), f L = S.map L

namespace StringTransducer

def equiv {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ') : StringTransducer α β σ' where
  start := equivσ S.start
  accept := S.accept.image equivσ
  step := fun (q : σ') (a : α) ↦ let ⟨q', w⟩ := S.step (equivσ.symm q) a ; (equivσ q', w)
  final := fun (q : σ') (h : _) ↦ S.final (equivσ.symm q) (Set.mem_image_equiv.mp h)

lemma equiv_equiv {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ') :
    (S.equiv equivσ).equiv equivσ.symm = S := by
  ext1
  · simp [equiv]
  · simp [equiv]
  · simp [equiv]
  · unfold equiv
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
    change
      let P := _
      (fun (q : _) (_ : q ∈ P) ↦ _) ≍ _
    intro P
    have : P = S.accept := Equiv.symm_image_image equivσ S.accept
    refine Function.hfunext rfl ?_
    intro q q' hq
    refine Function.hfunext ?_ ?_
    · rw [this]
      simp_all
    · intro h h' hh
      simp_all

instance {α β σ σ'} (S : StringTransducer α β σ) [DecidablePred (· ∈ S.accept)] (equivσ : σ ≃ σ') :
      DecidablePred (· ∈ (S.equiv equivσ).accept) := by
  unfold equiv
  simp only [Set.mem_image_equiv]
  exact inferInstance

lemma equiv_rewriteWithoutFinal {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ')
  (w : List α) (q : σ) :
    let ⟨q', w'⟩ := S.rewriteWithoutFinal q w
    (S.equiv equivσ).rewriteWithoutFinal (equivσ q) w = (equivσ q', w') := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [rewriteWithoutFinal_append, rewriteWithoutFinal, ih, List.append_nil, Prod.mk.eta,
      Prod.mk.injEq, List.append_cancel_left_eq]
    simp [equiv]

@[simp]
lemma equiv_start_eq {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ') :
    (S.equiv equivσ).start = equivσ S.start := rfl

@[simp]
lemma equiv_final_eq {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ') (q h) :
    (S.equiv equivσ).final (equivσ q) h = S.final q (by simpa [equiv] using h) := by
  simp [equiv]

@[simp]
lemma equiv_rewrite_eq {α β σ σ'} (S : StringTransducer α β σ) [DecidablePred (· ∈ S.accept)]
  (equivσ : σ ≃ σ') (w : List α) :
    (S.equiv equivσ).rewrite w = S.rewrite w := by
  unfold rewrite
  have := equiv_rewriteWithoutFinal S equivσ w S.start
  simp only [equiv_start_eq, this]
  split
  all_goals {
    rename_i h'
    simp only [equiv, Set.mem_image_equiv, Equiv.symm_apply_apply] at h'
    simp [h']
  }

@[simp]
lemma equiv_Rewrites_iff {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ')
  (w : List α) (w' : List β) :
    (S.equiv equivσ).Rewrites w w' ↔ S.Rewrites w w' := by
  classical
  simp [rewrite_eq_Rewrites]

@[simp]
lemma equiv_map_eq {α β σ σ'} (S : StringTransducer α β σ) (equivσ : σ ≃ σ') (L : Language α) :
    (S.equiv equivσ).map L = S.map L := by
  classical
  unfold map
  simp only [equiv_Rewrites_iff]
  trivial

lemma map_isStringTransduction {α β σ} [Finite σ] (S : StringTransducer α β σ) :
    Function.IsStringTransduction S.map := by
  have : Fintype σ := Fintype.ofFinite σ
  use Fintype.card σ, S.equiv (Fintype.equivFin σ)
  simp

structure Compose.accept_prop {α β₁ β₂ σ₁ σ₂}
    (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂)
    (q₁ : σ₁) (q₂ : σ₂) : Prop where
  q₁_accepts : q₁ ∈ S₁.accept
  q₂_leads_to_accept: (S₂.rewriteWithoutFinal q₂ (S₁.final q₁ q₁_accepts)).1 ∈ S₂.accept

def Compose {α β₁ β₂ σ₁ σ₂} (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂) :
    StringTransducer α β₂ (σ₁ × σ₂) where
  start := ⟨S₁.start, S₂.start⟩
  accept :=  { ⟨q₁,q₂⟩ : σ₁ × σ₂ | Compose.accept_prop S₁ S₂ q₁ q₂ }
  step := fun (q : σ₁ × σ₂) (a : α) ↦
    let ⟨q_in₁, q_in₂⟩ := q
    let ⟨q_out₁, w_out₁⟩ := S₁.step q_in₁ a
    let ⟨q_out₂, w_out₂⟩ := S₂.rewriteWithoutFinal q_in₂ w_out₁
    ⟨⟨q_out₁, q_out₂⟩, w_out₂⟩
  final := fun (q : σ₁ × σ₂) h ↦
    let ⟨q₁, q₂⟩ := q
    have h' : Compose.accept_prop S₁ S₂ q₁ q₂ := h
    --
    let final₁ := S₁.final q₁ h'.q₁_accepts
    --
    let tmp₂ := S₂.rewriteWithoutFinal q₂ final₁
    let q₂' := tmp₂.1
    let pre_final₂ := tmp₂.2
    --
    let final₂ := S₂.final q₂' (h'.q₂_leads_to_accept)
    --
    pre_final₂ ++ final₂

instance {α β₁ β₂ σ₁ σ₂}
  (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂)
  [DecidablePred (· ∈ S₁.accept)]
  [DecidablePred (· ∈ S₂.accept)] :
    DecidablePred (· ∈ (S₁.Compose S₂).accept) := by
  classical
  simp only [Compose, Set.mem_ofPred_eq]
  intro x
  if h1 : x.1 ∈ S₁.accept then
    if h2 : (S₂.rewriteWithoutFinal x.2 (S₁.final x.1 h1)).1 ∈ S₂.accept then
      exact isTrue ⟨h1, h2⟩
    else
      exact isFalse (by
        intro contra
        exact h2 contra.2 )
  else
    simp only
    exact isFalse (by
      intro contra
      exact h1 contra.1 )

@[simp]
lemma compose_rewriteWithoutFinal_eq {α β₁ β₂ σ₁ σ₂}
  (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂)
  (q₁ : σ₁) (q₂ : σ₂) (w : List α) :
    (Compose S₁ S₂).rewriteWithoutFinal (q₁, q₂) w =
      let ⟨q₁', w'⟩ := S₁.rewriteWithoutFinal q₁ w
      let ⟨q₂', w''⟩ := S₂.rewriteWithoutFinal q₂ w'
      ((q₁', q₂'), w'') := by
  induction w using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton xs x ih =>
    simp only [rewriteWithoutFinal_append, rewriteWithoutFinal, ih, List.append_nil, Prod.mk.eta,
      Prod.mk.injEq, List.append_cancel_left_eq]
    simp [Compose]

@[simp]
lemma compose_start_eq {α β₁ β₂ σ₁ σ₂}
  (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂) :
    (S₁.Compose S₂).start = (S₁.start, S₂.start) := rfl

@[simp]
lemma compose_rewrite_eq {α β₁ β₂ σ₁ σ₂ : Type*}
  (S₁ : StringTransducer α β₁ σ₁)
  (S₂ : StringTransducer β₁ β₂ σ₂)
  [DecidablePred (· ∈ S₁.accept)]
  [DecidablePred (· ∈ S₂.accept)]
  (w : List α) :
    (S₁.Compose S₂).rewrite w =
      (match S₁.rewrite w with | none => none | some u => S₂.rewrite u) := by
  unfold rewrite
  simp only [compose_start_eq, compose_rewriteWithoutFinal_eq]
  split
  · rename_i h1
    simp only [Compose, Set.mem_ofPred_eq] at h1
    simp only [h1.1, ↓reduceDIte, rewriteWithoutFinal_append, h1.2, List.append_assoc,
      Option.some.injEq, List.append_cancel_left_eq]
    rfl
  · rename_i h1
    simp only [Compose, Set.mem_ofPred_eq] at h1
    split
    · rename_i h2
      trivial
    · rename_i h2
      simp only [right_eq_dite_iff, reduceCtorEq, imp_false]
      intro contra
      simp only [Option.dite_none_right_eq_some, Option.some.injEq] at h2
      obtain ⟨h2, h2'⟩ := h2
      exact h1 ⟨ h2, by subst h2'; simp_all only [rewriteWithoutFinal_append] ⟩

@[simp]
lemma compose_defined {α β₁ β₂ σ₁ σ₂}
  (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂) :
    (S₁.Compose S₂).map = S₂.map ∘ S₁.map := by
  classical
  funext L
  ext1 w
  simp only [map, rewrite_eq_Rewrites, Function.comp_apply]
  constructor
  · intro h
    obtain ⟨u, hu, h⟩ := h
    simp only [compose_rewrite_eq] at h
    split at h
    · trivial
    · rename_i u' h2
      use u'
      simp only [h, and_true]
      exact ⟨u, ⟨hu, h2⟩⟩
  · intro h
    simp only [compose_rewrite_eq]
    obtain ⟨u, ⟨u', hu', hu''⟩, hu⟩ := h
    use u', hu'
    split
    · rename_i contra
      rw [contra] at hu''
      trivial
    · rename_i v hv
      rw [hu''] at hv
      simp only [Option.some.injEq] at hv
      subst u
      exact hu

def identity {α} : StringTransducer α α (Fin 1) where
  start := 0
  step := fun _ a ↦ (0, [a])
  accept := {0}
  final := fun _ _ ↦ []

instance {α} : DecidablePred (· ∈ (identity (α := α)).accept) := fun x ↦ isTrue x.fin_one_eq_zero

lemma identity_rewriteWithoutFinal {α} (w : List α) : 
    identity.rewriteWithoutFinal 0 w = (0,w) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton xs x ih =>
    simp only [Fin.isValue, rewriteWithoutFinal_append, rewriteWithoutFinal, ih, List.append_nil,
      Prod.mk.eta, Prod.mk.injEq, List.append_cancel_left_eq]
    exact ⟨rfl, rfl⟩

@[simp]
lemma identity_rewrite {α} (w : List α) : identity.rewrite w = w := by
  simp only [rewrite, Option.dite_none_right_eq_some, Option.some.injEq]
  have h1 : identity.start (α := α) = 0 := rfl
  have h2 : identity.accept (α := α) = {0} := rfl
  simp only [h1, Fin.isValue, identity_rewriteWithoutFinal, List.append_right_eq_self, h2,
    Set.mem_singleton_iff, exists_true_left]
  simp [identity]

@[simp]
lemma identity_map_eq_id {α} : identity.map = id (α := Language α) := by
  funext L
  simp only [id_eq]
  ext w
  simp only [map, rewrite_eq_Rewrites, identity_rewrite, Option.some.injEq, exists_eq_right]
  exact Iff.of_eq rfl

end StringTransducer 

theorem Function.compose_isStringTransduction {α β γ}
  (f : Language α → Language β)
  (g : Language β → Language γ)
  (hf : Function.IsStringTransduction f)
  (hg : Function.IsStringTransduction g) :
    Function.IsStringTransduction (g ∘ f) := by
  obtain ⟨nf, Sf, hf⟩ := hf
  obtain ⟨ng, Sg, hg⟩ := hg
  --
  have : f = Sf.map := by funext L; exact hf L
  have : g = Sg.map := by funext L; exact hg L
  subst f g
  rw [← StringTransducer.compose_defined]
  exact StringTransducer.map_isStringTransduction _

theorem Function.id_isStringTransduction {α} :
    Function.IsStringTransduction (id (α := Language α)) := ⟨1, StringTransducer.identity, by simp⟩

