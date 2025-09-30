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

-- def RewriteWordWithoutFinal₁ (s : List β) : σ → List α → σ × List β
--   | q, [] => (q, s)
--   | q, a :: as =>
--     let ⟨q', a'⟩ := 𝓣.step q a;
--     RewriteWordWithoutFinal₁ (s ++ a') q' as
--
-- def RewriteWordWithoutFinal : σ → List α → σ × List β := 𝓣.RewriteWordWithoutFinal₁ []

-- def Rewrites (source : σ × List α) : σ × List β :=
--   let ⟨q, w⟩ := source
--   w.foldr
--     (fun (a : α) (status : σ × List β) ↦
--       let ⟨q, v⟩ := status
--       let ⟨q',v'⟩ := 𝓣.step q a
--       (q', v ++ v'))
--     (q, [])

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

end StringTransducer
