/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import Mathlib.Data.List.Basic

@[simp]
theorem List.append_cancel_middle {α} {a b c : List α} :
    a ++ b ++ c = b ↔ a ++ c = [] := by
  constructor
  · intro h
    replace h := congrArg List.length h
    rw [List.length_append, List.length_append, Nat.add_comm, ← Nat.add_assoc] at h
    simp only [Nat.add_eq_right, Nat.add_eq_zero, length_eq_zero_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [append_nil]
  · intro h
    simp only [append_eq_nil_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [nil_append, append_nil]

theorem List.mem_iff_factor {α} {a : α} {s : List α} :
    a ∈ s ↔ ∃ n : Fin s.length, s = s.take n ++ [a] ++ s.drop (↑n + 1) := by
  constructor
  · intro h
    rw [List.mem_iff_get] at h
    obtain ⟨n, h⟩ := h
    have h' : s = s.take n ++ [s.get n] ++ s.drop (↑n + 1) := by
      simp only [get_eq_getElem, take_append_getElem, take_append_drop]
    rw [h] at h'
    exact ⟨n, h'⟩
  · intro h
    obtain ⟨n, h⟩ := h
    rw [h]
    simp only [append_assoc, cons_append, nil_append, mem_append, mem_cons, true_or, or_true]

theorem List.contains_two {α} {a b : α} {s : List α}
  (h₁ : a ≠ b) (h₂ : a ∈ s) (h₃ : b ∈ s) :
    (∃ x y z, s = x ++ [a] ++ y ++ [b] ++ z)
    ∨ (∃ x y z, s = x ++ [b] ++ y ++ [a] ++ z) := by
  induction s with
  | nil =>
    simp only [not_mem_nil] at h₂
  | cons c cs ih =>
    if h_na : c = a then
      left
      use []
      subst c
      simp only [nil_append, cons_append, append_assoc, cons.injEq, true_and]
      simp only [mem_cons] at h₃
      obtain h₃ | h₃ := h₃
      · exfalso
        exact h₁ (id (Eq.symm h₃))
      · rw [List.mem_iff_factor] at h₃
        obtain ⟨n, h₃⟩ := h₃
        simp only [append_assoc, cons_append, nil_append] at h₃
        exact ⟨_,_,h₃⟩
    else if h_nb : c = b then
      right
      use []
      subst c
      simp only [nil_append, cons_append, append_assoc, cons.injEq, true_and]
      simp only [mem_cons] at h₂
      obtain h₂ | h₂ := h₂
      · exfalso
        exact h₁ h₂
      · rw [List.mem_iff_factor] at h₂
        obtain ⟨n, h₂⟩ := h₂
        simp only [append_assoc, cons_append, nil_append] at h₂
        exact ⟨_,_,h₂⟩
    else
      simp only [mem_cons] at h₂
      simp only [mem_cons] at h₃
      --
      obtain h₂ | h₂ := h₂
      · exfalso
        exact h_na (id (Eq.symm h₂))
      --
      obtain h₃ | h₃ := h₃
      · exfalso
        exact h_nb (id (Eq.symm h₃))
      --
      replace ih := ih h₂ h₃
      obtain ⟨c',ih⟩ | ⟨c',ih⟩ := ih
      · left
        use c :: c'
        simp only [cons_append, append_assoc, nil_append, cons.injEq, true_and]
        simp only [append_assoc, cons_append, nil_append] at ih
        exact ih
      · right
        use c :: c'
        simp only [cons_append, append_assoc, nil_append, cons.injEq, true_and]
        simp only [append_assoc, cons_append, nil_append] at ih
        exact ih


