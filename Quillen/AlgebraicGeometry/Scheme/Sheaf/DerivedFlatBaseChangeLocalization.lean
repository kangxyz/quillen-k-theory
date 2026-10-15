/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeHorizontal
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeOpen
/-! # Target-open localization of the original derived flat base-change map

Horizontal pasting and invertibility of the original open-base-change mate identify local
invertibility with invertibility of the mate of the actual pasted cartesian square. Only the
second base leg is required to be open; the first remains flat.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard ambient categories. -/
local instance horizontalLocalizationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j) [Flat k] [Flat j]
/-- An actual target-open pullback detects the original derived mate via the pasted square. -/
theorem isIso_derivedFlatBaseChangeMap_pullback_iff [IsOpenImmersion k]
    (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    IsIso ((derivedFlatPullbackPlus k).map
      ((derivedFlatBaseChangeMap a b f j h).app K)) ↔
    IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have := isIso_derivedFlatBaseChangeMap_of_open c d b k hs
  rw [← derivedFlatBaseChangeMap_paste_horiz c d k a b f j hs h,
    derivedFlatBaseChangeHorizontalComposite_app]
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff]
end AlgebraicGeometry.Scheme.Modules
