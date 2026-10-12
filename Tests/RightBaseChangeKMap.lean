/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Map.RightBaseChange
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of original right-module change-of-rings K-map laws -/

@[expose] public section

noncomputable section

universe u

open Quillen.FiniteProjectiveModule

example (R : Type u) [Ring R] (n : ℕ) :
    (rightBaseChangeExact (RingHom.id R)).KMap n =
      MonoidHom.id ((exactStructure Rᵐᵒᵖ).K n) :=
  rightBaseChangeExact_KMap_id R n

example {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) (n : ℕ) :
    (rightBaseChangeExact (g.comp f)).KMap n =
      ((rightBaseChangeExact g).KMap n).comp ((rightBaseChangeExact f).KMap n) :=
  rightBaseChangeExact_KMap_comp f g n

example : (rightBaseChangeExact (RingHom.id (ZMod 1))).KMap 0 =
    MonoidHom.id ((exactStructure (ZMod 1)ᵐᵒᵖ).K 0) :=
  rightBaseChangeExact_KMap_id (ZMod 1) 0
