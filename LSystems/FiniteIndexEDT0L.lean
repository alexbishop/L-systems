/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Bishop
-/
module

public import LSystems.FiniteIndexEDT0L.Attach
public import LSystems.FiniteIndexEDT0L.Defs
public import LSystems.FiniteIndexEDT0L.LULT
public import LSystems.FiniteIndexEDT0L.Mapped
public import LSystems.FiniteIndexEDT0L.RegularLanguage
public import LSystems.FiniteIndexEDT0L.Union

/-!
# Finite Index EDT0L Languages

This file collects together the results on finite index EDT0L langyages.  In particular,
* `LSystems.FiniteIndexEDT0L.Defs`
  defines fintie index EDT0L languages
* `LSystems.FiniteIndexEDT0L.LULT`
  provides a defintion of *LULT* EDT0L grammars and languages; some basic results; and shows that
  a language is LULT if and only if it is EDT0L of finite index.
* `LSystems.FiniteIndexEDT0L.Attach`
  Shows that if `E` is a finite index EDT0L language, then so is `E.attach`.
* `LSystems.FiniteIndexEDT0L.Mapped`
  Proves that finite index EDT0L languages are closed under monoid homomorphism.
* `LSystems.FiniteIndexEDT0L.Union`
  The family of finite index EDT0L languages is closed under union.
* `LSystems.FiniteIndexEDT0L.RegularLanguage`
  If a language is regular (over a finite alphabet), then it is EDT0L of index 1 and thus EDT0L
  of finite index.
-/
