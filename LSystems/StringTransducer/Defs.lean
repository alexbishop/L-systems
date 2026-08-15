/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import Mathlib.Computability.Language

@[expose] public section

structure StringTransducer (α β σ : Type*) where
  start : σ
  accept : Set σ
  step : σ → α → (σ × List β)
  final : (q : σ) → (h : q ∈ accept) → List β

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

variable {α β σ} [Finite σ] (S : StringTransducer α β σ) in
lemma map_isStringTransduction : Function.IsStringTransduction S.map := by

  sorry


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

-- lemma Compose.left {α β₁ β₂ σ₁ σ₂}
--   (S₁ : StringTransducer α β₁ σ₁) [DecidablePred (· ∈ S₁.accept)]
--   (S₂ : StringTransducer β₁ β₂ σ₂) {u v} :
--     (S₁.Compose S₂).Rewrites u v → S₁.rewrite u ≠ .none := by
--   classical
--   -- intro h contra
--   -- unfold rewrite at contra
--   -- extract_lets wq q w at contra
--   -- split at contra
--   -- · trivial
--   -- --
--   -- rename_i hq
--   -- subst wq w q
--   -- --
--   -- rw [rewrite_eq_Rewrites, rewrite] at h
--   -- split at h
--   -- rotate_right
--   -- · trivial
--   -- --
--   -- rename_i hq'
--   -- clear * - hq hq'
--   -- have : ((S₁.Compose S₂).rewriteWithoutFinal (S₁.Compose S₂).start u).1.1
--   --           = (S₁.rewriteWithoutFinal S₁.start u).1 := by
--   --   induction u using List.reverseRec with
--   --   | nil =>
--   --     rfl
--   --   | append_singleton xs x ih =>
--   --     simp only [rewriteWithoutFinal_append, rewriteWithoutFinal, List.append_nil, Prod.mk.eta]
--   --     simp only [rewriteWithoutFinal_append, rewriteWithoutFinal, List.append_nil,
--   --       Prod.mk.eta] at hq'
--   --     
--   --
--   --     sorry
--
--   sorry

lemma Compose.defined {α β₁ β₂ σ₁ σ₂}
  (S₁ : StringTransducer α β₁ σ₁) (S₂ : StringTransducer β₁ β₂ σ₂) :
    (Compose S₁ S₂).map = S₂.map ∘ S₁.map := by
  classical
  funext L
  ext1 w
  constructor
  · intro h
    unfold map at ⊢ h
    unfold Compose at h
    simp_all only [Set.mem_setOf_eq, Function.comp_apply]
    --
    change let f : _ → _ := _ ; w ∈ {w | f w} at h
    extract_lets f at h
    change f w at h
    subst f
    obtain ⟨u, hu, h⟩ := h
    --
    change let f : _ → _ := _ ; w ∈ {w | f w}
    extract_lets f
    change f w
    subst f
    simp only
    conv =>
      arg 1
      intro u
      lhs
      tactic =>
        change let f : _ → _ := _ ; (u ∈ {w | f w}) = _
        extract_lets f
        change f u = _
        subst f
    simp only [rewrite_eq_Rewrites]
    simp only [rewrite_eq_Rewrites] at h
    

    sorry
  · intro h

    sorry




end StringTransducer 


-- @[simp]
-- lemma rewriteWithoutFinal_nil (q : σ) : S.rewriteWithoutFinal q [] = (q, []) := rfl
--
-- @[simp]
-- lemma rewriteWithoutFinal_single (q : σ) (a : α) :
--     st.rewriteWithoutFinal q [a] = st.step q a := by
--   unfold rewriteWithoutFinal
--   simp only [rewriteWithoutFinal_nil, List.append_nil]
--
-- lemma rewriteWithoutFinal_cons (q : σ) (a : α) (as : List α) :
--     let status₁ := st.rewriteWithoutFinal q [a];
--     let status₂ := st.rewriteWithoutFinal status₁.1 as;
--     --
--     st.rewriteWithoutFinal q (a::as) = ⟨status₂.1, status₁.2 ++ status₂.2⟩ := by
--   intro status₁ status₂
--   unfold rewriteWithoutFinal
--   split
--   rename_i q' a' h₁
--   split
--   rename_i q'' as' h₂
--   --
--   subst status₁
--   subst status₂
--   --
--   ext1 <;> (simp only; rw [rewriteWithoutFinal_single, h₁, h₂])

-- lemma rewriteWithoutFinal_append (q : σ) (a b : List α) :
--     let status₁ := st.rewriteWithoutFinal q a;
--     let status₂ := st.rewriteWithoutFinal status₁.1 b;
--     --
--     st.rewriteWithoutFinal q (a ++ b) = ⟨status₂.1, status₁.2 ++ status₂.2⟩ := by
--   induction a with
--   | nil =>
--     simp only [List.nil_append, rewriteWithoutFinal_nil]
--   | cons a as ih =>
--     extract_lets s₁ s₂
--     extract_lets t₁ t₂ at ih
--     rw [List.cons_append]
--     conv => lhs; rw [rewriteWithoutFinal_cons]
--
--     sorry


