/-
Copyright (c) 2025 Alex Bishop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alex Bishop
-/
module

public import LSystems.EDT0L
public import LSystems.FiniteIndexEDT0L

/-!
# L-Systems

This library contains an implementation of some of the known results concerning EDT0L systems.  The
goal of this project is to provide a big enough framework in order to formalise the known results in
group theory that make use of EDT0L languages.

The main concepts of this library can be found in
* `LSystems.EDT0L` where we define the class of EDT0L languages and prove some of their closure
    properties; and
* `LSystems.FiniteIndexEDT0L` where we define the class of EDT0L languages of finite index, we
    consider one equivalent definition, and we prove some of their closure properties.
-/
