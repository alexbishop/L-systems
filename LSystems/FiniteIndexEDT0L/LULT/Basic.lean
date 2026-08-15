/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.FiniteIndexEDT0L.Defs
public import LSystems.FiniteIndexEDT0L.LULT.Defs

import LSystems.FiniteIndexEDT0L.LULT.LULTImpFiEDT0L
import LSystems.FiniteIndexEDT0L.LULT.FiEDT0LImpLULT

@[expose] public section

@[simp]
theorem Language.isLULT_iff_isFiniteIndexEDT0L {α} (L : Language α) :
    L.IsLULT ↔ L.IsFiniteIndexEDT0L :=
  ⟨L.isLULT_imp_isFiniteIndexEDT0L, L.isFiniteIndexEDT0L_imp_isLULT⟩

