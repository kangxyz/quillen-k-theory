/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedOpenBaseChange

/-! Consumers retain the actual module base-change map, both original units, and derived arrows. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
namespace QuillenTest.DerivedOpenBaseChange

open Quillen
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

lemma original_unit_square {Z U X : Scheme.{u}} (f : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (K : CochainComplex.Plus Z.Modules) :
    (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K) ≫
      (derivedRestrictionPlus j).map ((derivedPushforwardPlusUnit f).app K) ≫
      (derivedPushforwardPlusOpenBaseChange f j).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (AlgebraicGeometry.Scheme.Modules.openBaseChange f
          j)).hom.app K) ≫
      (derivedPushforwardPlusUnit (pullback.snd f j)).app
        ((Scheme.Modules.restrictFunctor (pullback.fst f j)).mapCochainComplexPlus.obj K) ≫
      (derivedPushforwardPlus (pullback.snd f j)).map
        ((Scheme.Modules.restrictFunctor (pullback.fst f j)).rightDerivedFunctorPlusUnit.app K) :=
  by
  simpa only [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc,
    derivedRestrictionPlus, derivedPushforwardPlus, derivedPushforwardPlusUnit] using
    derivedPushforwardPlusOpenBaseChange_unit f j K

lemma original_derived_naturality {Z U X : Scheme.{u}} (f : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] {K L : DerivedCategory.Plus Z.Modules} (g : K ⟶ L) :
    (derivedRestrictionPlus j).map ((derivedPushforwardPlus f).map g) ≫
        (derivedPushforwardPlusOpenBaseChange f j).hom.app L =
      (derivedPushforwardPlusOpenBaseChange f j).hom.app K ≫
        (derivedPushforwardPlus (pullback.snd f j)).map
          ((derivedRestrictionPlus (pullback.fst f j)).map g) :=
  (derivedPushforwardPlusOpenBaseChange f j).hom.naturality g

lemma original_derived_inverse {Z U X : Scheme.{u}} (f : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategory.Plus Z.Modules) :
    (derivedPushforwardPlusOpenBaseChange f j).hom.app K ≫
      (derivedPushforwardPlusOpenBaseChange f j).inv.app K = 𝟙 _ :=
  (derivedPushforwardPlusOpenBaseChange f j).hom_inv_id_app K

lemma original_restriction_unit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex.Plus X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusUnit.app K) := by
  let := isIso_derivedRestrictionPlusUnit j
  infer_instance

end QuillenTest.DerivedOpenBaseChange
