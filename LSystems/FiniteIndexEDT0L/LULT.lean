/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.FiniteIndexEDT0L.LULT.Defs
public import LSystems.FiniteIndexEDT0L.LULT.Basic
public import LSystems.FiniteIndexEDT0L.LULT.Attach

/-!
# LULT Languages

This file collects together results on LULT languages.  In particular, it includes the following:
* `LSystems.FiniteIndexEDT0L.LULT.Defs`
  Definition of LULT grammars
* `LSystems.FiniteIndexEDT0L.LULT.Basis`
  currently only contains the theorem `Language.isLULT_iff_isFiniteIndexEDT0L`
* `LSystems.FiniteIndexEDT0L.LULT.Attach`
  Shows that if `E` is a LULT ET0L language, then `E.attach` is also LULT
-/


