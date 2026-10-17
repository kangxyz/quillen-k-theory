/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.AffineLocal
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Vertical
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.SingleAcyclicity
/-! # Original affine-composite chart base change -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived category of module sheaves. -/
local instance affineCompositeBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j) [Flat j]
  [IsAffineHom g] [IsAffineHom (g ≫ f)] (N : Z.Modules) [N.IsQuasicoherent]

include hs

/-- Vertical pasting identifies the original mate on the actual derived chart direct image. -/
theorem isIso_derivedFlatBaseChangeMap_affineDerivedImage :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((derivedPushforwardPlus g).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj N))) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d g a hs
  have := isIso_derivedFlatBaseChangeMap_affineHom_single c d g a hs N
  have hb := isIso_derivedFlatBaseChangeMap_affineHom_single c (d ≫ b) (g ≫ f) j
    (hs.paste_vert h) N
  rw [← derivedFlatBaseChangeMap_paste_vert c d g a b f j hs h,
    derivedFlatBaseChangeVerticalComposite_app] at hb
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff] at hb
  exact hb

/-- The same original mate is invertible on the actual ordinary chart direct image. -/
theorem isIso_derivedFlatBaseChangeMap_affinePushforward_single :
    IsIso ((derivedFlatBaseChangeMap a b f j h).app
      ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj
        ((Scheme.Modules.pushforward g).obj N))) := by
  have := isIso_derivedPushforwardPlusUnit_single g N
  exact (NatTrans.isIso_app_iff_of_iso (derivedFlatBaseChangeMap a b f j h)
    (derivedPushforwardPlusSingleIso g N)).mp
      (isIso_derivedFlatBaseChangeMap_affineDerivedImage c d g a b f j hs h N)

end AlgebraicGeometry.Scheme.Modules
