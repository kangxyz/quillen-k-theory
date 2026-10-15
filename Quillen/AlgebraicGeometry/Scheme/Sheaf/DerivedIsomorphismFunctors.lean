/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianIsomorphismBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedPushforwardSection
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatPullbackComposition

/-! # Derived functors and base change for scheme isomorphisms -/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard module-sheaf derived categories. -/
local instance isomorphismBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [IsIso f] [Flat j]
/-- Base change of an isomorphism preserves the original derived flat mate on all D+ objects. -/
theorem isIso_derivedFlatBaseChangeMap_of_isIso :
    letI := flat_cartesian_baseChange a b f j h
    IsIso (derivedFlatBaseChangeMap a b f j h) := by
  let := flat_cartesian_baseChange a b f j h
  let := h.isIso_snd_of_isIso
  let := pushforward_isEquivalence_of_isIso b
  let F := Scheme.Modules.pushforward f
  let J := Scheme.Modules.pullback j
  let P := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward b
  have := isIso_cartesianBaseChangeMap_of_isIso a b f j h
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  let := P.isRightDerivedFunctor_comp_of_preservesHomology G
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

namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard module-sheaf derived categories. -/
local instance derivedIsomorphismStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
/-- Original geometric direct images of mutually inverse morphisms give an actual equivalence. -/
theorem derivedPushforwardPlus_isEquivalence_of_isIso :
    (derivedPushforwardPlus f).IsEquivalence :=
  Functor.IsEquivalence.mk' (derivedPushforwardPlus (inv f))
    (derivedPushforwardPlusSectionIso f (inv f) (IsIso.hom_inv_id f)).symm
    (derivedPushforwardPlusSectionIso (inv f) f (IsIso.inv_hom_id f))
/-- The original derived flat pullback along an actual scheme isomorphism is an equivalence. -/
theorem derivedFlatPullbackPlus_isEquivalence_of_isIso :
    (derivedFlatPullbackPlus f).IsEquivalence := by
  let eY : derivedFlatPullbackPlus f ⋙ derivedFlatPullbackPlus (inv f) ≅
      𝟭 (DerivedCategory.Plus Y.Modules) :=
    derivedFlatPullbackPlusCompIso (inv f) f ≪≫
      (Scheme.Modules.pullback (inv f ≫ f)).rightDerivedFunctorPlusIso
        (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId Y) ≪≫
      Functor.rightDerivedFunctorPlusIdIso Y.Modules
  let eX : derivedFlatPullbackPlus (inv f) ⋙ derivedFlatPullbackPlus f ≅
      𝟭 (DerivedCategory.Plus X.Modules) :=
    derivedFlatPullbackPlusCompIso f (inv f) ≪≫
      (Scheme.Modules.pullback (f ≫ inv f)).rightDerivedFunctorPlusIso
        (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f) ≪≫ Scheme.Modules.pullbackId X) ≪≫
      Functor.rightDerivedFunctorPlusIdIso X.Modules
  exact Functor.IsEquivalence.mk' (derivedFlatPullbackPlus (inv f)) eY.symm eX
end AlgebraicGeometry.Scheme.Modules
