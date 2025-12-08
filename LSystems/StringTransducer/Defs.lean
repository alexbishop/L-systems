/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import Mathlib.Computability.Language

structure StringTransducer (α β σ : Type*) [Fintype α] [Fintype β] [Fintype σ] where
  start : σ
  accept : Finset σ
  step : σ → α → (σ × List β)
  final : (q : σ) → q ∈ accept → List β

namespace StringTransducer
variable {α β σ : Type*} [Fintype α] [Fintype β] [Fintype σ]
variable (𝓣 : StringTransducer α β σ)

def RewriteWordWithoutFinal : σ → List α → σ × List β
  | q, [] => (q, [])
  | q, a :: as =>
    let ⟨q_next, head⟩ := 𝓣.step q a;
    let ⟨q_last, tail⟩ := RewriteWordWithoutFinal q_next as;
    (q_last, head ++ tail)

def Generates (source : List α) (target : List β) : Prop :=
  let ⟨q, w⟩ := 𝓣.RewriteWordWithoutFinal 𝓣.start source
  ∃ h : q ∈ 𝓣.accept, target = w ++ 𝓣.final q h

def map (L : Language α) : Language β := 
  { w : List β | ∃ u ∈ L, 𝓣.Generates u w}

namespace RewriteWordWithoutFinal

@[simp]
lemma refl (q : σ) : 𝓣.RewriteWordWithoutFinal q [] = (q, []) := rfl

lemma single (q : σ) (a : α) :
    𝓣.RewriteWordWithoutFinal q [a] = 𝓣.step q a := by
  unfold RewriteWordWithoutFinal
  simp only [refl, List.append_nil]

@[simp]
lemma cons (q : σ) (a : α) (as : List α) :
    let status₁ := 𝓣.RewriteWordWithoutFinal q [a];
    let status₂ := 𝓣.RewriteWordWithoutFinal status₁.1 as;
    --
    𝓣.RewriteWordWithoutFinal q (a::as) = ⟨status₂.1, status₁.2 ++ status₂.2⟩ := by
  intro status₁ status₂
  unfold RewriteWordWithoutFinal
  split
  rename_i q' a' h₁
  split
  rename_i q'' as' h₂
  --
  subst status₁
  subst status₂
  --
  ext1 <;> (simp only; rw [single, h₁, h₂])

-- lemma append (q : σ) (a b : List α) :
--     let status₁ := 𝓣.RewriteWordWithoutFinal q a;
--     let status₂ := 𝓣.RewriteWordWithoutFinal status₁.1 b;
--     --
--     𝓣.RewriteWordWithoutFinal q (a ++ b) = ⟨status₂.1, status₁.2 ++ status₂.2⟩ := by
--   intro status₁ status₂
--   induction a with
--   | nil =>
--     subst status₁ status₂
--     simp only [refl, List.nil_append]
--   | cons a as ih =>
--     extract_lets status₁' status₂' at ih
--     rw [List.cons_append, cons]
--     -- simp only [ih]
--
--     sorry


end RewriteWordWithoutFinal
end StringTransducer
