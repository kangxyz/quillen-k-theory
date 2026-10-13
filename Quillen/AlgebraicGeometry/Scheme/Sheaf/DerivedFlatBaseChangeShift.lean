/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChange
public import Quillen.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusCompositionShift
public import Quillen.CategoryTheory.Functor.Derived.RightDerivedShift
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedPushforwardSection

/-! # Shift compatibility of the actual derived flat base-change mate -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
/-- The standard ambient derived categories of the original module sheaves. -/
local instance shiftStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
/-- The exact flat pullback retains its installed shift comparison. -/
instance derivedFlatPullbackPlusCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (derivedFlatPullbackPlus f).CommShift ℤ := by
  unfold derivedFlatPullbackPlus
  infer_instance
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
/-- The literal derived mate respects the installed shifts. -/
theorem derivedFlatBaseChangeMap_commShift :
    letI := flat_cartesian_baseChange a b f j h
    NatTrans.CommShift (derivedFlatBaseChangeMap a b f j h) ℤ := by
  let := flat_cartesian_baseChange a b f j h
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let P := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward b
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  unfold derivedFlatBaseChangeMap
  apply Functor.commShift_rightDerivedDesc (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus)
end Quillen.SchemeSheaf
