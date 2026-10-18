/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionAutomorphismCones
public import Quillen.KTheory.Plus.ProjectiveCompletionFiberFormula
public import Quillen.CategoryTheory.GroupCompletion.StableGeneralLinearMap

/-!
# The actual fixed-denominator contraction of finite completion stages

The fixed-denominator inclusion retains the original extension projection.
The native completion identity entry, restricted to a finite matrix stage,
is exactly the fixed-denominator identity-extension diagram. The original
subdivision contraction therefore gives a specified homotopy of that actual
localized stage map to the fixed-denominator zero extension.

This is a source-family homotopy in the localized total extension space.
Its comparison with the stored homotopy-fiber path and the capped positive
Q-cylinder remains open; no matrix marking is asserted here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  inflationDirectSumAction extensionDirectSumAction identityExtensionLinear
  identityExtensionPairLinear extensionPairProjectionLinear
  extensionProjectionLinear
variable (R : Type u) [Ring R]

/-- Include the original extension category with the specified denominator unchanged. -/
def fixedDenominatorExtension (P : IsoCategory R) :
    (exactStructure R).ExtensionTotal ⥤ LocalizedExtensionCategory R where
  obj X := localizedExtensionPair R P X
  map f := GroupCompletion.ActionLocalization.ofHom (𝟙 P, f)
  map_id X := GroupCompletion.ActionLocalization.ofHom_id (P, X)
  map_comp {X Y Z} f g := by
    simpa using (GroupCompletion.ActionLocalization.ofHom_comp
      (C := IsoCategory R) (X := (P, X)) (Y := (P, Y)) (Z := (P, Z))
      (𝟙 P, f) (𝟙 P, g))

/-- The actual fixed-denominator Q projection is the original extension projection. -/
theorem fixedDenominatorExtension_projection (P : IsoCategory R) :
    fixedDenominatorExtension R P ⋙ localizedExtensionProjection R =
      (exactStructure R).extensionProjection := by
  let : MonoidalLeftAction (IsoCategory R) (exactStructure R).QCategory :=
    MonoidalLeftAction.trivial _ _
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have h := GroupCompletion.ActionLocalization.mapFunctor_ofHom (C := IsoCategory R)
    (extensionPairProjection R) (X := (P, X)) (Y := (P, Y)) (𝟙 P, f)
  let G := GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor
    (IsoCategory R) (exactStructure R).QCategory
  exact (congrArg G.map h).trans
    (GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor_map_ofHom
      (C := IsoCategory R) _)

/-- The original core enters completion with the specified fixed denominator. -/
def fixedDenominatorCore (P : IsoCategory R) : IsoCategory R ⥤ GroupCompletionCategory R where
  obj X := completionPair R P X
  map f := GroupCompletion.ActionLocalization.ofHom (𝟙 P, f)
  map_id X := GroupCompletion.ActionLocalization.ofHom_id (P, X)
  map_comp {X Y Z} f g := by
    simpa using (GroupCompletion.ActionLocalization.ofHom_comp
      (C := IsoCategory R) (X := (P, X)) (Y := (P, Y)) (Z := (P, Z))
      (𝟙 P, f) (𝟙 P, g))

/-- The actual completion identity entry retains this fixed-denominator extension diagram. -/
theorem fixedDenominatorCore_identityEntry (P : IsoCategory R) :
    fixedDenominatorCore R P ⋙ completionIdentityEntry R =
      (exactStructure R).identityExtensionFunctor ⋙ fixedDenominatorExtension R P := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact GroupCompletion.ActionLocalization.mapFunctor_ofHom (identityExtensionPairFunctor R) _

/-- The original finite-stage matrix functor has the displayed fixed denominator and
power action. -/
theorem stageFunctor_fixedDenominator (n : ℕ) :
    StableCompletion.stageFunctor R n =
      (AsSmall.down ⋙ StableFree.powerFunctor R n) ⋙
        fixedDenominatorCore Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Apply the original subdivision contraction inside the actual fixed-denominator total space. -/
def fixedDenominatorContraction (P : IsoCategory R) :
    ((classifyingSpaceMapUniversal (fixedDenominatorExtension R P)).comp
      (classifyingSpaceMapUniversal (exactStructure R).identityExtensionFunctor)).Homotopy
        (ContinuousMap.const _
          (classifyingSpacePoint ((fixedDenominatorExtension R P).obj
            (exactStructure R).extensionTotalPoint))) := by
  let H := (ContinuousMap.Homotopy.refl
      (classifyingSpaceMapUniversal (fixedDenominatorExtension R P))).comp
    ((exactStructure R).extensionTotalContraction.compContinuousMap
      (classifyingSpaceMapUniversal (exactStructure R).identityExtensionFunctor))
  exact H.cast rfl (by ext x; exact classifyingSpaceMapUniversal_point _ _)


/-- The native finite-stage identity-entry functor is exactly the displayed extension diagram. -/
theorem stageIdentity_fixedDenominator (n : ℕ) :
    StableCompletion.stageFunctor R n ⋙ completionIdentityEntry Rᵐᵒᵖ =
      (AsSmall.down ⋙ StableFree.powerFunctor R n) ⋙
        ((exactStructure Rᵐᵒᵖ).identityExtensionFunctor ⋙
          fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)) := by
  rw [stageFunctor_fixedDenominator, CategoryTheory.Functor.assoc,
    fixedDenominatorCore_identityEntry]

/-- The actual native stage map contracts to its original fixed-denominator zero extension. -/
def stageIdentityContraction (n : ℕ) :
    (classifyingSpaceMapUniversal
      (StableCompletion.stageFunctor R n ⋙ completionIdentityEntry Rᵐᵒᵖ)).Homotopy
        (ContinuousMap.const _ (classifyingSpacePoint
          ((fixedDenominatorExtension Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)).obj
            (exactStructure Rᵐᵒᵖ).extensionTotalPoint))) := by
  let H := (fixedDenominatorContraction Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n)).compContinuousMap
    (classifyingSpaceMapUniversal (AsSmall.down ⋙ StableFree.powerFunctor R n))
  refine H.cast ?_ rfl
  simp only [stageIdentity_fixedDenominator, classifyingSpaceMapUniversal_comp]

end Quillen.FiniteProjectiveModule
