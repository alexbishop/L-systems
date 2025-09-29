/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import LSystems.EDT0L.Defs

namespace EDT0LGrammar
variable {T N₀ H₀ N₁ H₁ : Type*} [Fintype N₀] [Fintype H₀] [Fintype N₁] [Fintype H₁]

structure UnionData where
  E₀ : EDT0LGrammar T N₀ H₀
  E₁ : EDT0LGrammar T N₁ H₁

namespace UnionData
variable (𝓖 : @UnionData T N₀ H₀ N₁ H₁ _ _ _ _)

def extend_alphabet₀ : Symbol T N₀ → Symbol T ((N₀ ⊕ N₁) ⊕ Unit)
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (.inl (.inl n))

def extend_alphabet₁ : Symbol T N₁ → Symbol T ((N₀ ⊕ N₁) ⊕ Unit)
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (.inl (.inr n))

section extend_alphabets
variable {T N₀ N₁ : Type*}

@[simp]
lemma extend_alphabet₀_terminal (t : T) :
    @extend_alphabet₀ T N₀ N₁ (.terminal t) = (.terminal t) := rfl

@[simp]
lemma extend_alphabet₁_terminal (t : T) :
    @extend_alphabet₁ T N₀ N₁ (.terminal t) = (.terminal t) := rfl

@[simp]
lemma extend_alphabet₀_nonterminal (n : N₀) :
    @extend_alphabet₀ T N₀ N₁ (.nonterminal n) = (.nonterminal <| .inl <| .inl <| n) := rfl

@[simp]
lemma extend_alphabet₁_nonterminal (n : N₁) :
    @extend_alphabet₁ T N₀ N₁ (.nonterminal n) = (.nonterminal <| .inl <| .inr <| n) := rfl

@[simp]
lemma extend_alphabet₀_terminal_word (w : List T) :
    List.map (@extend_alphabet₀ T N₀ N₁) (List.map .terminal w)
    = List.map .terminal w := by
  --
  induction w
  · simp only [List.map_nil]
  · rename_i a as ih
    simp_all only [
      List.map_map, List.map_inj_left,
      Function.comp_apply, List.map_cons, List.cons.injEq, implies_true,
      and_true]
    rfl

@[simp]
lemma extend_alphabet₁_terminal_word (w : List T) :
    List.map (@extend_alphabet₁ T N₀ N₁) (List.map .terminal w)
    = List.map .terminal w := by
  --
  induction w
  · simp only [List.map_nil]
  · rename_i a as ih
    simp_all only [
      List.map_map, List.map_inj_left,
      Function.comp_apply, List.map_cons, List.cons.injEq, implies_true,
      and_true]
    rfl

end extend_alphabets

def grammar : EDT0LGrammar T ((N₀ ⊕ N₁) ⊕ Unit) ((H₀ ⊕ H₁) ⊕ Fin 2) where
  initial := .inr ()
  tables := fun h n ↦ match h with
    | .inl (.inl τ₀) => match n with
      | .inl (.inl n₀) => (𝓖.E₀.tables τ₀ n₀).map extend_alphabet₀
      | _ => [.nonterminal n]
    | .inl (.inr τ₁) => match n with
      | .inl (.inr n₁) => (𝓖.E₁.tables τ₁ n₁).map extend_alphabet₁
      | _ => [.nonterminal n]
    | .inr 0 => match n with
      | .inl s => [.nonterminal (.inl s)]
      | .inr _ => [.nonterminal (.inl (.inl 𝓖.E₀.initial))]
    | .inr 1 => match n with
      | .inl s => [.nonterminal (.inl s)]
      | .inr _ => [.nonterminal (.inl (.inr 𝓖.E₁.initial))]

lemma left_rewrites (w : List (Symbol T ((N₀ ⊕ N₁) ⊕ Unit)))
  (w' : List (Symbol T ((N₀ ⊕ N₁) ⊕ Unit)))
  (h : ∃ u : List (Symbol T N₀), w = u.map extend_alphabet₀ ∧ 𝓖.E₀.Generates u) :
    𝓖.grammar.Rewrites w w'
      → ∃ u' : List (Symbol T N₀), w' = u'.map extend_alphabet₀ ∧ 𝓖.E₀.Generates u' := by
  --
  intro h₁
  have ⟨u, ⟨h_l, h_r⟩⟩ := h
  clear h
  unfold EDT0LGrammar.Rewrites at h₁
  unfold EDT0LGrammar.RewriteWord at h₁
  unfold EDT0LGrammar.RewriteSymbol at h₁
  unfold UnionData.grammar at h₁
  unfold extend_alphabet₀ at h_l
  simp only at h₁
  subst h_l
  replace ⟨τ, h₁⟩ := h₁
  simp [List.flatMap_map] at h₁
  match τ with
  | .inl (.inl τ₀) =>
      simp only at h₁
      change
        let inner := _;
        @List.flatMap _ _ inner _ = _
        at h₁
      extract_lets inner at h₁
      have hh : inner = fun a ↦ List.map extend_alphabet₀ (𝓖.E₀.RewriteSymbol τ₀ a) := by
        unfold extend_alphabet₀
        unfold inner
        funext a
        subst h₁
        clear τ
        --FIXME aesop?
        split
        · rename_i x t heq
          split at heq
          · rename_i x_1 t_1
            simp_all only [Symbol.terminal.injEq]
            subst heq
            rfl
          · rename_i x_1 n
            simp_all only [reduceCtorEq]
        · rename_i x n heq
          cases n with
          | inl val =>
            cases val with
            | inl val_1 =>
              simp_all only
              split at heq
              next x_1 t => simp_all only [reduceCtorEq]
              next x_1 n =>
                simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq]
                subst heq
                rfl
            | inr val_2 =>
              simp_all only
              split at heq
              next x_1 t => simp_all only [reduceCtorEq]
              next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
          | inr val_1 =>
            simp_all only
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
      rw [hh] at h₁
      clear hh
      clear inner

      rw [← List.flatMap_map] at h₁
      rw [← List.map_flatMap] at h₁
      change
        let u' := _;
        List.map extend_alphabet₀ u' = _
        at h₁
      extract_lets u' at h₁
      use u'
      constructor
      · exact Eq.symm h₁
      · have hh : 𝓖.E₀.Rewrites u u' := by
          use τ₀
          unfold RewriteWord
          subst u'
          rw [List.flatMap_id', ← List.flatMap_def]
        unfold EDT0LGrammar.Generates
        unfold EDT0LGrammar.Generates at h_r
        unfold EDT0LGrammar.Derives
        unfold EDT0LGrammar.Derives at h_r
        exact Relation.ReflTransGen.tail h_r hh
  | .inl (.inr τ₁) =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₀ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq]
              subst heq
              rfl
          | inr val_2 =>
            simp_all only [List.map_eq_singleton_iff]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r
  | .inr 0 =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₀ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq]
              subst heq
              rfl
          | inr val_2 =>
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r
  | .inr 1 =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₀ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq]
              subst heq
              rfl
          | inr val_2 =>
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r

lemma right_rewrites (w : List (Symbol T ((N₀ ⊕ N₁) ⊕ Unit)))
  (w' : List (Symbol T ((N₀ ⊕ N₁) ⊕ Unit)))
  (h : ∃ u : List (Symbol T N₁), w = u.map extend_alphabet₁ ∧ 𝓖.E₁.Generates u) :
    𝓖.grammar.Rewrites w w'
      → ∃ u' : List (Symbol T N₁), w' = u'.map extend_alphabet₁ ∧ 𝓖.E₁.Generates u' := by
  intro h₁
  have ⟨u, ⟨h_l, h_r⟩⟩ := h
  clear h
  unfold EDT0LGrammar.Rewrites at h₁
  unfold EDT0LGrammar.RewriteWord at h₁
  unfold EDT0LGrammar.RewriteSymbol at h₁
  unfold UnionData.grammar at h₁
  unfold extend_alphabet₁ at h_l
  simp only at h₁
  subst h_l
  replace ⟨τ, h₁⟩ := h₁
  simp [List.flatMap_map] at h₁
  match τ with
  | .inl (.inr τ₁) =>
      simp only at h₁
      change
        let inner := _;
        @List.flatMap _ _ inner _ = _
        at h₁
      extract_lets inner at h₁
      have hh : inner = fun a ↦ List.map extend_alphabet₁ (𝓖.E₁.RewriteSymbol τ₁ a) := by
        unfold extend_alphabet₁
        unfold inner
        funext a
        subst h₁
        clear τ
        --FIXME aesop?
        split
        next x t heq =>
          split at heq
          next x_1 t_1 =>
            simp_all only [Symbol.terminal.injEq]
            subst heq
            rfl
          next x_1 n => simp_all only [reduceCtorEq]
        next x n heq =>
          cases n with
          | inl val =>
            cases val with
            | inl val_1 =>
              simp_all only
              split at heq
              next x_1 t => simp_all only [reduceCtorEq]
              next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
            | inr val_2 =>
              simp_all only
              split at heq
              next x_1 t => simp_all only [reduceCtorEq]
              next x_1 n =>
                simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, Sum.inr.injEq]
                subst heq
                rfl
          | inr val_1 =>
            simp_all only
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
      rw [hh] at h₁
      clear hh
      clear inner

      rw [← List.flatMap_map] at h₁
      rw [← List.map_flatMap] at h₁
      change
        let u' := _;
        List.map extend_alphabet₁ u' = _
        at h₁
      extract_lets u' at h₁
      use u'
      constructor
      · exact Eq.symm h₁
      · have hh : 𝓖.E₁.Rewrites u u' := by
          use τ₁
          unfold RewriteWord
          subst u'
          rw [List.flatMap_id', ← List.flatMap_def]
        unfold EDT0LGrammar.Generates
        unfold EDT0LGrammar.Generates at h_r
        unfold EDT0LGrammar.Derives
        unfold EDT0LGrammar.Derives at h_r
        exact Relation.ReflTransGen.tail h_r hh
  | .inl (.inl τ₀) =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₁ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.map_eq_singleton_iff]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
          | inr val_2 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, Sum.inr.injEq]
              subst heq
              rfl
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r
  | .inr 0 =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₁ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
          | inr val_2 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, Sum.inr.injEq]
              subst heq
              rfl
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r
  | .inr 1 =>
    simp only at h₁
    change
      let inner := _;
      @List.flatMap _ _ inner _ = _
      at h₁
    extract_lets inner at h₁
    have hh : inner = fun a ↦ [extend_alphabet₁ a] := by
      unfold inner
      funext a
      clear h₁
      clear inner
      clear τ
      -- aesop
      split
      next x t heq =>
        simp_all only [List.cons.injEq, and_true]
        split at heq
        next x_1 t_1 =>
          simp_all only [Symbol.terminal.injEq]
          subst heq
          rfl
        next x_1 n => simp_all only [reduceCtorEq]
      next x n heq =>
        cases n with
        | inl val =>
          cases val with
          | inl val_1 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
          | inr val_2 =>
            simp_all only [List.cons.injEq, and_true]
            split at heq
            next x_1 t => simp_all only [reduceCtorEq]
            next x_1 n =>
              simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, Sum.inr.injEq]
              subst heq
              rfl
        | inr val_1 =>
          simp_all only [List.cons.injEq, and_true]
          split at heq
          next x_1 t => simp_all only [reduceCtorEq]
          next x_1 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
    use u
    rw [← h₁, hh]
    constructor
    · rw [← List.map_eq_flatMap]
    · exact h_r

lemma basic_property
  (w : List (Symbol T ((N₀ ⊕ N₁) ⊕ Unit)))
  (h : 𝓖.grammar.Generates w) :
    w = [.nonterminal 𝓖.grammar.initial]
    ∨ (∃ u : List (Symbol T N₀), w = u.map extend_alphabet₀ ∧ 𝓖.E₀.Generates u)
    ∨ (∃ u : List (Symbol T N₁), w = u.map extend_alphabet₁ ∧ 𝓖.E₁.Generates u) := by
  --
  induction h
  case refl => left; rfl
  case tail a b ih₁ ih₂ ih₃ =>
    cases ih₃
    · rename_i ih₃
      -- we are rewriting the starting symbol
      replace ⟨τ, ih₂⟩ := ih₂
      match τ with
      | .inl (.inl τ₀) =>
        left
        rw [← ih₂, ih₃]
        unfold EDT0LGrammar.RewriteWord
        unfold EDT0LGrammar.RewriteSymbol
        unfold UnionData.grammar
        simp only
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      | .inl (.inr τ₁) =>
        left
        rw [← ih₂, ih₃]
        unfold EDT0LGrammar.RewriteWord
        unfold EDT0LGrammar.RewriteSymbol
        unfold UnionData.grammar
        simp only
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      | .inr 0 =>
        right ; left
        use [.nonterminal 𝓖.E₀.initial]
        constructor
        · rw [← ih₂, ih₃]
          unfold extend_alphabet₀
          unfold EDT0LGrammar.RewriteWord
          unfold EDT0LGrammar.RewriteSymbol
          unfold UnionData.grammar
          simp only
          rw [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        · unfold EDT0LGrammar.Generates
          unfold EDT0LGrammar.Derives
          exact Relation.ReflTransGen.refl
      | .inr 1 =>
        right ; right
        use [.nonterminal 𝓖.E₁.initial]
        constructor
        · rw [← ih₂, ih₃]
          unfold extend_alphabet₁
          unfold EDT0LGrammar.RewriteWord
          unfold EDT0LGrammar.RewriteSymbol
          unfold UnionData.grammar
          simp only
          rw [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        · unfold EDT0LGrammar.Generates
          unfold EDT0LGrammar.Derives
          exact Relation.ReflTransGen.refl
    · rename_i ih₃
      cases ih₃
      · rename_i ih₃
        right; left
        exact 𝓖.left_rewrites a b ih₃ ih₂
      · rename_i ih₃
        right; right
        exact 𝓖.right_rewrites a b ih₃ ih₂

lemma basic_property₀
  (w : List (Symbol T N₀))
  (h : 𝓖.E₀.Generates w) :
    𝓖.grammar.Generates (w.map extend_alphabet₀) := by
  --
  induction h
  case refl =>
    unfold EDT0LGrammar.Generates
    unfold EDT0LGrammar.Derives
    apply Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) ?_
    unfold EDT0LGrammar.Rewrites
    use .inr 0
    unfold EDT0LGrammar.RewriteWord
    unfold EDT0LGrammar.RewriteSymbol
    unfold UnionData.grammar
    simp only
    unfold extend_alphabet₀
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
  case tail x y z ih₁ ih₂ =>
    have hh :
        𝓖.grammar.Rewrites
          (List.map extend_alphabet₀ x)
          (List.map extend_alphabet₀ y) := by
      have ⟨ τ, h ⟩ := ih₁
      rw [← h]
      use .inl (.inl τ)
      unfold EDT0LGrammar.RewriteWord
      unfold EDT0LGrammar.RewriteSymbol
      unfold UnionData.grammar
      --
      unfold extend_alphabet₀
      simp only
      simp only [List.flatMap_map, List.map_flatMap]
      clear h
      clear z
      change
        let f_l := List.flatMap _;
        let f_r := List.flatMap _;
        f_l x = f_r x
      extract_lets f_l f_r
      have hh : f_l = f_r := by
        unfold f_l
        unfold f_r
        funext xx
        induction xx
        · simp only [List.flatMap_nil]
        · rename_i a as ih
          -- aesop
          simp_all only [List.flatMap_cons, List.append_cancel_right_eq]
          split
          next x_1 t heq =>
            split
            next x_2 t_1 => simp_all only [Symbol.terminal.injEq, List.map_cons, List.map_nil]
            next x_2 n => simp_all only [reduceCtorEq]
          next x_1 n heq =>
            cases n with
            | inl val =>
              cases val with
              | inl val_1 =>
                simp_all only
                split
                next x_2 t => simp_all only [reduceCtorEq]
                next x_2 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq]
              | inr val_2 =>
                simp_all only
                split
                next x_2 t => simp_all only [reduceCtorEq]
                next x_2 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
            | inr val_1 =>
              simp_all only
              split
              next x_2 t => simp_all only [reduceCtorEq]
              next x_2 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
      rw [hh]
    unfold EDT0LGrammar.Generates
    unfold EDT0LGrammar.Generates at ih₂
    unfold EDT0LGrammar.Derives
    unfold EDT0LGrammar.Derives at ih₂
    exact Relation.ReflTransGen.tail ih₂ hh

lemma basic_property₁
  (w : List (Symbol T N₁))
  (h : 𝓖.E₁.Generates w) :
    𝓖.grammar.Generates (w.map extend_alphabet₁) := by
  --
  induction h
  case refl =>
    unfold EDT0LGrammar.Generates
    unfold EDT0LGrammar.Derives
    apply Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) ?_
    unfold EDT0LGrammar.Rewrites
    use .inr 1
    unfold EDT0LGrammar.RewriteWord
    unfold EDT0LGrammar.RewriteSymbol
    unfold UnionData.grammar
    simp only
    unfold extend_alphabet₁
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
  case tail x y z ih₁ ih₂ =>
    have hh :
        𝓖.grammar.Rewrites
          (List.map extend_alphabet₁ x)
          (List.map extend_alphabet₁ y) := by
      have ⟨ τ, h ⟩ := ih₁
      rw [← h]
      use .inl (.inr τ)
      unfold EDT0LGrammar.RewriteWord
      unfold EDT0LGrammar.RewriteSymbol
      unfold UnionData.grammar
      --
      unfold extend_alphabet₁
      simp only
      simp only [List.flatMap_map, List.map_flatMap]
      clear h
      clear z
      change
        let f_l := List.flatMap _;
        let f_r := List.flatMap _;
        f_l x = f_r x
      extract_lets f_l f_r
      have hh : f_l = f_r := by
        unfold f_l
        unfold f_r
        funext xx
        induction xx
        · simp only [List.flatMap_nil]
        · rename_i a as ih
          -- aesop
          simp_all only [List.flatMap_cons, List.append_cancel_right_eq]
          split
          next x_1 t heq =>
            split
            next x_2 t_1 => simp_all only [Symbol.terminal.injEq, List.map_cons, List.map_nil]
            next x_2 n => simp_all only [reduceCtorEq]
          next x_1 n heq =>
            cases n with
            | inl val =>
              cases val with
              | inl val_1 =>
                simp_all only
                split
                next x_2 t => simp_all only [reduceCtorEq]
                next x_2 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, reduceCtorEq]
              | inr val_2 =>
                simp_all only
                split
                next x_2 t => simp_all only [reduceCtorEq]
                next x_2 n => simp_all only [Symbol.nonterminal.injEq, Sum.inl.injEq, Sum.inr.injEq]
            | inr val_1 =>
              simp_all only
              split
              next x_2 t => simp_all only [reduceCtorEq]
              next x_2 n => simp_all only [Symbol.nonterminal.injEq, reduceCtorEq]
      rw [hh]
    unfold EDT0LGrammar.Generates
    unfold EDT0LGrammar.Generates at ih₂
    unfold EDT0LGrammar.Derives
    unfold EDT0LGrammar.Derives at ih₂
    exact Relation.ReflTransGen.tail ih₂ hh

theorem defines_union : 𝓖.grammar.language = 𝓖.E₀.language + 𝓖.E₁.language := by
  rw [Language.add_def]
  unfold EDT0LGrammar.language
  --
  have h (w : List T) :
      𝓖.grammar.Generates (List.map Symbol.terminal w)
      ↔ 𝓖.E₀.Generates (List.map Symbol.terminal w)
        ∨ 𝓖.E₁.Generates (List.map Symbol.terminal w) := by
    --
    constructor
    · intro h
      replace h := 𝓖.basic_property _ h
      match h with
      | .inl h =>
        exfalso
        -- aesop?
        simp_all only [
          true_or, List.map_eq_singleton_iff, reduceCtorEq, and_false, exists_false]
      | .inr (.inl h') =>
        --
        replace h := h'
        clear h'
        left
        replace ⟨u, ⟨h_l, h_r⟩⟩ := h
        have hh : List.map Symbol.terminal w = u := by
          clear h_r
          clear h
          induction u generalizing w
          · simp_all only [List.map_nil, List.map_eq_nil_iff]
          · rename_i a as ih
            -- unfold extend_alphabet₀ at ih
            simp_all only [List.map_cons]
            have hh : w ≠ [] := by
              simp_all only [ne_eq]
              intro a_1
              subst a_1
              simp_all only [List.map_nil, List.nil_eq, reduceCtorEq]
            replace hh : ∃ b bs, w = b :: bs := by
              exact List.ne_nil_iff_exists_cons.mp hh
            replace ⟨b, bs, hh⟩ := hh
            subst hh
            unfold List.map
            conv at h_l =>
              lhs
              unfold List.map
            replace ih := ih bs
            have h₁ : Symbol.terminal b = @extend_alphabet₀ T N₀ N₁ a := by
              simp_all only [List.cons.injEq, forall_const]
            have h₂ :
                List.map Symbol.terminal bs =
                List.map (@extend_alphabet₀ T N₀ N₁) as := by
              simp_all only [List.cons.injEq, true_and, forall_const]
            replace ih := ih h₂
            rw [← ih]
            unfold extend_alphabet₀ at h₁
            replace h₁ : Symbol.terminal b = a := by
              match a with
              | .terminal t =>
                subst ih
                simp_all only [
                  Symbol.terminal.injEq,
                  List.map_map, List.map_inj_left, Function.comp_apply,
                  List.cons.injEq, implies_true, and_true]
              | .nonterminal n =>
                simp only at h₁
                exfalso
                simp_all only [reduceCtorEq]
            rw [h₁]
        rw [hh]
        exact h_r
      | .inr (.inr h') =>
        --
        replace h := h'
        clear h'
        right
        replace ⟨u, ⟨h_l, h_r⟩⟩ := h
        have hh : List.map Symbol.terminal w = u := by
          clear h_r
          clear h
          induction u generalizing w
          · simp_all only [List.map_nil, List.map_eq_nil_iff]
          · rename_i a as ih
            -- unfold extend_alphabet₀ at ih
            simp_all only [List.map_cons]
            have hh : w ≠ [] := by
              simp_all only [ne_eq]
              intro a_1
              subst a_1
              simp_all only [List.map_nil, List.nil_eq, reduceCtorEq]
            replace hh : ∃ b bs, w = b :: bs := by
              exact List.ne_nil_iff_exists_cons.mp hh
            replace ⟨b, bs, hh⟩ := hh
            subst hh
            unfold List.map
            conv at h_l =>
              lhs
              unfold List.map
            replace ih := ih bs
            have h₁ : Symbol.terminal b = @extend_alphabet₁ T N₀ N₁ a := by
              simp_all only [List.cons.injEq, forall_const]
            have h₂ :
                List.map Symbol.terminal bs =
                List.map (@extend_alphabet₁ T N₀ N₁) as := by
              simp_all only [List.cons.injEq, true_and, forall_const]
            replace ih := ih h₂
            rw [← ih]
            unfold extend_alphabet₁ at h₁
            replace h₁ : Symbol.terminal b = a := by
              match a with
              | .terminal t =>
                subst ih
                simp_all only [
                  Symbol.terminal.injEq,
                  List.map_map, List.map_inj_left, Function.comp_apply,
                  List.cons.injEq, implies_true, and_true]
              | .nonterminal n =>
                simp only at h₁
                exfalso
                simp_all only [reduceCtorEq]
            rw [h₁]
        rw [hh]
        exact h_r
    · intro h
      cases h
      · rename_i h
        have hh := 𝓖.basic_property₀ _ h
        rw [extend_alphabet₀_terminal_word] at hh
        exact hh
      · rename_i h
        have hh := 𝓖.basic_property₁ _ h
        rw [extend_alphabet₁_terminal_word] at hh
        exact hh
  exact Language.ext_iff.mpr h

end UnionData

theorem closed_under_union (L₁ L₂ : Language T)
  (h₁ : L₁.IsEDT0L)
  (h₂ : L₂.IsEDT0L) :
    (L₁ + L₂).IsEDT0L := by
  have ⟨_, _ , E₁, P₁⟩ := h₁
  have ⟨_, _ , E₂, P₂⟩ := h₂
  let union_data := UnionData.mk E₁ E₂
  have h := union_data.defines_union
  have ⟨n,m,E',P'⟩ := union_data.grammar.edt0l_grammars_generate_edt0l_languages
  use n, m, E'
  rw [P', h]
  unfold union_data
  rw [P₁, P₂]

end EDT0LGrammar
