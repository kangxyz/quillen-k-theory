/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Horizontal
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.OpenImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackSingle

/-! # Original base-open localization of the derived flat mate -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived category of module sheaves. -/
local instance baseOpenStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j)

/-- Localizing the original base retains the same derived mate on the actual restricted sheaf. -/

theorem isIso_derivedFlatBaseChangeMap_baseOpen_single_iff [Flat k] [IsOpenImmersion j]
    (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap c d b k hs).app
      ((DerivedCategory.Plus.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pullback a).obj M))) ↔
    IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have := isIso_derivedFlatBaseChangeMap_of_open a b f j h
  apply (NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap c d b k hs)
    (derivedFlatPullbackPlusSingleIso a M)).symm.trans
  rw [← derivedFlatBaseChangeMap_paste_horiz c d k a b f j hs h,
    derivedFlatBaseChangeHorizontalComposite_app]
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]

end AlgebraicGeometry.Scheme.Modules
