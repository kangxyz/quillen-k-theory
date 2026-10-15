/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianOpenBaseChangeMate
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction

/-! # The original derived flat base-change mate on open immersions -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- Original standard ambient derived categories. -/
local instance openMateStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
/-- Open pullback preserves injectives via the original restriction iso. -/
instance pullback_preservesInjectiveObjects_of_open {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : (Scheme.Modules.pullback j).PreservesInjectiveObjects where
  injective_obj {M} hM := Injective.of_iso ((Scheme.Modules.restrictFunctorIsoPullback j).app M)
    ((Scheme.Modules.restrictFunctor j).injective_obj_of_injective hM)
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion j] (h : IsPullback a b f j)
/-- The original derived flat mate is invertible on all bounded-below complexes
under open base change. -/
theorem isIso_derivedFlatBaseChangeMap_of_open :
    IsIso (derivedFlatBaseChangeMap a b f j h) := by
  let : IsOpenImmersion a := MorphismProperty.of_isPullback h.flip inferInstance
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let P := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward b
  have := isIso_cartesianBaseChangeMap_of_open a b f j h
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  let := P.isRightDerivedFunctor_comp_of_preservesInjectiveObjects G
  let e := (F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus).rightDerivedNatIso
    (P.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit F J)
    (Functor.rightDerivedFunctorPlusCompUnit P G) (CochainComplex.Plus.quasiIso U.Modules)
    (Functor.isoWhiskerRight
      (NatIso.mapCochainComplexPlus (asIso (cartesianBaseChangeMap a b f j h)))
      DerivedCategory.Plus.Q)
  change IsIso e.hom
  infer_instance
end AlgebraicGeometry.Scheme.Modules
