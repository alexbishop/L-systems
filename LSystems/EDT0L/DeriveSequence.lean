import LSystems.EDT0L.Defs

namespace EDT0LGrammar
variable {T N H : Type*} [Fintype H] [Fintype N] (E : EDT0LGrammar T N H)

def DeriveSequence (s : List H) (w : List (Symbol T N)) : List (Symbol T N) :=
  List.foldl (fun w' τ ↦ E.RewriteWord τ w') w s

namespace DeriveSequence
@[simp]
lemma derives_seq_refl (w : List (Symbol T N)) :
    E.DeriveSequence [] w = w := rfl

@[simp]
lemma rewrite_word_iff_derive_seq_singleton (w : List (Symbol T N)) (τ : H) :
    E.RewriteWord τ w = E.DeriveSequence [τ] w := rfl

lemma rewrites_iff_derive_seq_singleton (w w' : List (Symbol T N)) :
    E.Rewrites w w' ↔ ∃ τ : H, E.DeriveSequence [τ] w = w' := by
  constructor
  · intro h
    unfold Rewrites at h
    simp only [rewrite_word_iff_derive_seq_singleton] at h
    exact h
  · intro h
    replace ⟨τ, h⟩ := h
    unfold Rewrites
    rw [← rewrite_word_iff_derive_seq_singleton] at h
    exact ⟨τ, h⟩

@[simp]
lemma derives_iff_derive_seq (w w' : List (Symbol T N)) :
    E.Derives w w' ↔ ∃ s : List H, E.DeriveSequence s w = w' := by
  --
  constructor
  · intro h
    induction h with
    | refl =>
      use []
      rw [derives_seq_refl]
    | tail h₁ h₂ h₃ =>
      replace ⟨τ, h₂⟩ := h₂
      replace ⟨s, h₃⟩ := h₃
      use s ++ [τ]
      unfold DeriveSequence
      unfold DeriveSequence at h₃
      rw [List.foldl_append, h₃, List.foldl_cons, List.foldl_nil]
      exact h₂
  · intro h
    replace ⟨s, h⟩ := h
    induction s using List.reverseRecOn generalizing w w' with
    | nil =>
      rw [derives_seq_refl] at h
      rw [h]
      exact Relation.ReflTransGen.refl
    | append_singleton as a ih =>
      unfold DeriveSequence at h
      rw [List.foldl_append] at h
      change
        let w'' := E.DeriveSequence _ _;
        List.foldl _ w'' _ = _
        at h
      extract_lets w'' at h
      replace ih := ih w w''
      unfold w'' at ih
      simp only [forall_const] at ih
      change E.Derives _ w'' at ih
      rw [List.foldl_cons, List.foldl_nil] at h
      exact Derives.tail ih ⟨a, h⟩

end DeriveSequence
end EDT0LGrammar

