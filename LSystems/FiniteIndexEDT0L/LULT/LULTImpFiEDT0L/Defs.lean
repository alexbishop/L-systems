/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
import Mathlib.Tactic

import LSystems.FiniteIndexEDT0L.LULT.Defs
import LSystems.FiniteIndexEDT0L.Defs
import LSystems.EDT0L.Defs
import LSystems.EDT0L.DeriveSequence
import LSystems.EDT0L.DeadEnds
import LSystems.EDT0L.ReachableTerminals

namespace EDT0LGrammar

namespace LULTImpFiEDT0L

/-- A word in the letters α of length either zero or one.

Note that α is the type of terminal letters. -/
inductive SmallWord (α : Type*) where
| epsilon
| letter (a : α)
deriving DecidableEq, Fintype

/-- The number of times a nonterminal appears in the expansion of a LULT grammar.

Note that α is the type of terminal letters. -/
inductive StatusOfNonterminal (α : Type*) where
| zero
| one
| many (w : SmallWord α)
deriving DecidableEq, Fintype

/-- A map from nonterminals to their status. -/
def StatusOfAllNonterminals (α V : Type*) := V → StatusOfNonterminal α

variable (α V : Type*) [Fintype V] [DecidableEq α] [DecidableEq V] in
deriving instance DecidableEq for StatusOfAllNonterminals α V

variable (α V : Type*) [Fintype α] [Fintype V] [DecidableEq V] in
deriving instance Fintype for StatusOfAllNonterminals α V

/-- The set of nonterminals for our constructed language.

Here
 * α is a finite set of terminal letters that can appear in the output
 * V is the set of nonterminals in the original EDT0L language -/
inductive Nonterminal (α V : Type*) [Fintype α] [Fintype V] where
| start
| dead
| single (b : V) (status: StatusOfAllNonterminals α V)
| ender (status: StatusOfAllNonterminals α V)
deriving DecidableEq

instance (α V : Type*) [Fintype α] [Fintype V] [DecidableEq α] [DecidableEq V] :
    Fintype (Nonterminal α V) := derive_fintype% _

/-- Used to contruct the tables of an ET0L grammar.

Here:
  * α is the type of terminals of the LULT grammar
  * V is the type of nonterminals of the LULT grammar
  * T is the type of tables of the LULT grammar
-/
inductive Table (α V T : Type*) [Fintype α] [Fintype V] [Fintype T] where
| start
| final
| step (pre_table : T) (status: StatusOfAllNonterminals α V)
deriving DecidableEq

instance (α V T : Type*)
  [Fintype α] [Fintype V] [Fintype T]
  [DecidableEq α] [DecidableEq V] [DecidableEq T] :
    Fintype (Table α V T) := derive_fintype% _

end LULTImpFiEDT0L

namespace LULTImpFiEDT0L
variable {α V T : Type*}
variable [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
variable (E : EDT0LGrammar α V T)

abbrev annotated_tables := LULTImpFiEDT0L.Table E.visible_terminals V T
abbrev annotated_nonterminals := LULTImpFiEDT0L.Nonterminal E.visible_terminals V
abbrev annotated_symbols := Symbol α (annotated_nonterminals E)
abbrev status_all_nonterminals := StatusOfAllNonterminals E.visible_terminals V
end LULTImpFiEDT0L

namespace LULTImpFiEDT0L

/-- A technical definition used to define `IsValidReplacement` -/
@[simp]
def validReplacement.expressions_match' {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T)
  (f : status_all_nonterminals E)
  (v : V)
  (expanded : List α) : Prop :=
  match f v with
  | .one | .zero => true
  | .many .epsilon => expanded = []
  | .many <| .letter t => expanded = [t]

variable {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  (E : EDT0LGrammar α V T)
  (f : status_all_nonterminals E)
  (v : V)
  (expanded : List α) in
instance : Decidable (validReplacement.expressions_match' E f v expanded) := by
  unfold validReplacement.expressions_match' 
  split <;> exact inferInstance

namespace status_all_nonterminals
def domain {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E) :
    Finset V :=
  { v | f v ≠ .one ∧ f v ≠ .zero}

def range_at_table {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f : status_all_nonterminals E)
  (t : T) :
    Finset V :=
  Finset.sup f.domain
    fun x ↦ ({ n | .nonterminal n ∈ E.tables t x } : Finset V)
end status_all_nonterminals

structure validReplacement {α V T : Type*}
  [Fintype V] [Fintype T] [DecidableEq α] [DecidableEq V] [DecidableEq T]
  {E : EDT0LGrammar α V T}
  (f g : status_all_nonterminals E)
  (t : T) : Prop where
valid_composition : 
  let f_codomain := status_all_nonterminals.range_at_table f t;
  let g_domain := status_all_nonterminals.domain g;
  f_codomain ⊆ g_domain
expansions_match :
  ∀ n,
    let expanded : List α :=
      (E.tables t n).flatMap fun x ↦
        match x with
        | .terminal t => [t]
        | .nonterminal x =>
          match g x with
          | .many <| .letter t => [t]
          | _ => []
    validReplacement.expressions_match' E f n expanded
nodup_ensure_one :
  ∀ n (_ : g n = .one), ∑ x with f x = .one, (E.tables t x).count (.nonterminal n) = 1
nodup_ensure_zero :
  ∀ n (_ : g n = .zero) x (_ : f x = .one), .nonterminal n ∉ (E.tables t x)

variable {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  (E : EDT0LGrammar T N H)
  (f g : status_all_nonterminals E)
  (h : H) in
instance : Decidable (validReplacement f g h) :=
  if h₁ : _  then
    if h₂ : _ then
      if h₃ : _ then
        if h₄ : _ then
          isTrue ⟨h₁, h₂, h₃, h₄⟩
        else
          isFalse (by intro contra; exact h₄ contra.nodup_ensure_zero)
      else
        isFalse (by intro contra; exact h₃ contra.nodup_ensure_one)
    else
      isFalse (by intro contra; exact h₂ contra.expansions_match)
  else
      isFalse (by intro contra; exact h₁ contra.valid_composition)

@[simp]
def rewriteSymbol {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  {E : EDT0LGrammar T N H}
  (g : status_all_nonterminals E)
  (n : N) (h : H) :
    List (annotated_symbols E) :=
  (E.tables h n).flatMap fun x ↦
    match x with 
    | .terminal t => [.terminal t]
    | .nonterminal v =>
      match g v with
      | .one => [.nonterminal <| .single v g]
      | .zero => []
      | .many .epsilon => []
      | .many <| .letter t => [.terminal t]

end LULTImpFiEDT0L

def LULTImpFiEDT0L {T N H : Type*}
  [Fintype N] [Fintype H] [DecidableEq T] [DecidableEq N] [DecidableEq H]
  (E : EDT0LGrammar T N H) :
    EDT0LGrammar
      T
      (LULTImpFiEDT0L.annotated_nonterminals E)
      (LULTImpFiEDT0L.annotated_tables E) where
  initial := .start
  tables := fun t v ↦
    --
    match t with
    | .start =>
      match v with
      | .start =>
        let f : _ := fun n ↦ if n = E.initial then .one else .zero;
        --
        [.nonterminal <| .single E.initial f,
         .nonterminal <| .ender f]
      | .ender _ | .dead =>
        [.nonterminal .dead]
      | _ => []
    | .final =>
      match v with
      | .ender f => 
        if f = (fun _ ↦ .zero)
        then []
        else [.nonterminal .dead]
      | .dead | .start =>
        [.nonterminal .dead]
      | _ => []
    | .step t' f' =>
      match v with
      | .start | .dead =>
        [.nonterminal .dead]
      | .single v f =>
        if LULTImpFiEDT0L.validReplacement f f' t'
        then LULTImpFiEDT0L.rewriteSymbol f' v t'
        else []
      | .ender f =>
        if LULTImpFiEDT0L.validReplacement f f' t'
        then [.nonterminal <| .ender <| f']
        else [.nonterminal .dead]

end EDT0LGrammar
