/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Original bounded-below derived direct image under open base change

The original module-sheaf base-change isomorphism is derived using exactness of open restriction
and its preservation of injectives. The result needs only the actual open immersion, without
quasicoherence, affine, finite, flat or noetherian assumptions on the direct-image morphism.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules


open ModuleCat




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard ambient derived categories used by the original functors. -/
local instance derivedOpenBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The actual original open base-change isomorphism for bounded-below derived direct image. -/
def derivedPushforwardPlusOpenBaseChange {Z U X : Scheme.{u}}
    (f : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j] :
    derivedPushforwardPlus f ⋙ derivedRestrictionPlus j ≅
      derivedRestrictionPlus (pullback.fst f j) ⋙ derivedPushforwardPlus (pullback.snd f j) :=
  ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
  (Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusIso
    (AlgebraicGeometry.Scheme.Modules.openBaseChange f j) ≪≫
  Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives
    (Scheme.Modules.restrictFunctor (pullback.fst f j))
    (Scheme.Modules.pushforward (pullback.snd f j))

/-- The derived open base-change comparison retains the original module-sheaf base-change map
and the composite original derived units. -/
lemma derivedPushforwardPlusOpenBaseChange_unit {Z U X : Scheme.{u}}
    (f : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex.Plus Z.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.restrictFunctor j)).app K ≫
      (derivedPushforwardPlusOpenBaseChange f j).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (AlgebraicGeometry.Scheme.Modules.openBaseChange f
          j)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.restrictFunctor (pullback.fst f j))
        (Scheme.Modules.pushforward (pullback.snd f j))).app K := by
  let F := Scheme.Modules.pushforward f
  let A := Scheme.Modules.restrictFunctor j
  let P := Scheme.Modules.restrictFunctor (pullback.fst f j)
  let G := Scheme.Modules.pushforward (pullback.snd f j)
  let eL := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology A
  let eM := (F ⋙ A).rightDerivedFunctorPlusIso (AlgebraicGeometry.Scheme.Modules.openBaseChange f j)
  let eR := P.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G
  have hL := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app A K
  have hM := (F ⋙ A).rightDerivedFunctorPlusIso_hom_app
    (AlgebraicGeometry.Scheme.Modules.openBaseChange f j) K
  have hR := P.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app G K
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app F A K] at hL
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app P G K] at hR
  change _ ≫ (eL.inv.app _ ≫ eM.hom.app _ ≫ eR.hom.app _) = _
  dsimp only [eL, eM, eR]
  rw [← hL]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hM, Category.assoc, hR]

end AlgebraicGeometry.Scheme.Modules
