/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[simp]
theorem Finset.sum_nat_eq_one {α : Type*} {s : Finset α} {f : α → ℕ} :
    ∑ x ∈ s, f x = 1 ↔ ∃ x ∈ s, (f x = 1 ∧ ∀ y ∈ s, (y ≠ x → f y = 0)) := by
  have _ : DecidableEq α := Classical.typeDecidableEq α
  constructor
  · intro h
    have h_ne_zero : ∑ x ∈ s, f x ≠ 0 := ne_zero_of_eq_one h
    by_cases h₁ : ∀ x ∈ s, f x = 0
    · exfalso
      rw [← Finset.sum_eq_zero_iff (f := f)] at h₁
      exact h_ne_zero h₁
    · simp only [not_forall] at h₁
      obtain ⟨x, hx, h₁⟩ := h₁
      rw [Finset.sum_eq_add_sum_diff_singleton (f := f) hx] at h
      match h₃ : f x with
      | 0 =>
        exfalso
        exact h₁ h₃
      | n + 2 =>
        exfalso
        simp only [Nat.succ_eq_add_one] at h₃
        rw [h₃] at h
        simp only [Nat.add_assoc] at h
        rw [Nat.add_comm] at h
        simp only [Nat.add_assoc] at h
        simp only [Nat.add_eq_left, Nat.add_eq_zero, one_ne_zero, false_and] at h
      | 1 =>
        rw [h₃] at h
        simp only [Nat.add_eq_left, sum_eq_zero_iff, mem_sdiff, mem_singleton, and_imp] at h
        exact ⟨x, hx, h₃, h⟩
  · intro h
    obtain ⟨x, hx, ⟨h₁, h₂⟩⟩ := h
    rw [Finset.sum_eq_add_sum_diff_singleton (f := f) hx, h₁]
    simp only [Nat.add_eq_left, sum_eq_zero_iff, mem_sdiff, mem_singleton, and_imp]
    exact h₂

