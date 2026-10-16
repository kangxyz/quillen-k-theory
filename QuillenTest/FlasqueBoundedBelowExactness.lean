/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlasqueBoundedBelow

/-! # Original Godement totalization exactness consumers

These clients exercise the actual total functor's addition, zero object and
pushout maps, retaining the original inherited cofibration predicate.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes
open scoped ZeroObject

namespace FlasqueBoundedBelowExactnessConsumers

/-- The actual lifted total functor sends the original sum to the mapped sum. -/
theorem original_total_map_add (X : Scheme.{u}) {K L : BoundedBelow.Obj X}
    (f g : K ⟶ L) :
    (FlasqueBoundedBelow.total X).map (f + g) =
      (FlasqueBoundedBelow.total X).map f + (FlasqueBoundedBelow.total X).map g :=
  (FlasqueBoundedBelow.total X).map_add (f := f) (g := g)

/-- The chosen original zero object remains zero under the actual total functor. -/
theorem original_total_zero (X : Scheme.{u}) :
    IsZero ((FlasqueBoundedBelow.total X).obj (0 : BoundedBelow.Obj X)) :=
  (FlasqueBoundedBelow.total_exact X).zero (isZero_zero _)

/-- Actual admissible pushout squares retain all four original mapped arrows. -/
theorem original_total_pushout (X : Scheme.{u}) {A B D T : BoundedBelow.Obj X}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T}
    (hi : (BoundedBelow.waldhausen X).cof i) (h : IsPushout i f g j) :
    IsPushout ((FlasqueBoundedBelow.total X).map i)
      ((FlasqueBoundedBelow.total X).map f) ((FlasqueBoundedBelow.total X).map g)
      ((FlasqueBoundedBelow.total X).map j) :=
  (FlasqueBoundedBelow.total_exact X).pushout hi h

end FlasqueBoundedBelowExactnessConsumers
