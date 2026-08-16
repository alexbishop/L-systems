/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bishop
-/
module

public import LSystems.EDT0L.Defs
public import LSystems.EDT0L.Basic
public import LSystems.EDT0L.DeadEnds
public import LSystems.EDT0L.RewriteSequence
public import LSystems.EDT0L.Attach
public import LSystems.EDT0L.Mapped
public import LSystems.EDT0L.Union
public import LSystems.EDT0L.RegularLanguage

/-!
# EDT0L Languages

This file collects together the results on EDT0L languages, in particular, this file imports the
following

* `LSystems.EDT0L.Defs`
  where EDT0L grammars, EDT0L languages, and a basic result are proven **(start here)**
* `LSystems.EDT0L.Basic`
  where some basic tools and results are proven.  The results in this file either do not fit
  anywhere else, or are useful for other proofs involving EDT0L languages.
* `LSystems.EDT0L.DeadEnds`
  which provides results on *dead ends* which is a common tool used to simplify the construction of
  EDT0L grammars.
* `LSystems.EDT0L.RewriteSequence`
  which provides an alternative definition of what it means for an EDT0L grammar to *derive* a word
  from another word.  The definitions and theorems provided in this file greatly simplify many
  results, and are necesary to define the classes of *finite index* and *LULT* EDT0L languages.
* `LSystems.EDT0L.Attach`
  Words which appear in an EDT0L language can only have letters which come from some finite type.
  This file contains technical definitions and lemmas which allow us to restrict ourselves to such a
  fintie type.  The purpose of this file is to help simplify some other proofs in the project.
* `LSystems.EDT0L.Mapped`
  Proves that the class of EDT0L languages is closed under application of monoid homomorphism.
* `LSystems.EDT0L.Union`
  The family of EDT0L languages is closed under union.
* `LSystems.EDT0L.RegularLanguage`
  If a language is regular (over a finite alphabet), then it is EDT0L.
-/
