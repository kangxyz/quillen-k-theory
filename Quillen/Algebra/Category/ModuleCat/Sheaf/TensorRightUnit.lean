/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.Sheaf.Tensor

/-!
# The original right tensor unit

The right-unit natural isomorphism is the original presheaf right unitor
followed by the module-sheafification counit. All site and coefficient
universes and sheafification hypotheses remain explicit. This constructs
only the right-unit comparison, without asserting full monoidal coherence.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SheafOfModulesOfCommRing
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- The actual sheaf tensor with the structure module on the right is naturally the identity. -/
def tensorRightUnitIso :
    tensorFunctor R ⋙ (CategoryTheory.evaluation _ _).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
      𝟭 (SheafOfModulesOfCommRing R) :=
  Functor.isoWhiskerLeft (toPresheaf R)
      (Functor.isoWhiskerRight (rightUnitorNatIso
        (PresheafOfModulesOfCommRing.{u} R.obj)) (associatedSheaf R)) ≪≫
    asIso (PresheafOfModules.sheafificationAdjunction
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (𝟙 _)).counit
/-- The original right unitor followed by the actual sheafification counit is the forward map. -/
theorem tensorRightUnitIso_hom_app (M : SheafOfModulesOfCommRing R) :
    (tensorRightUnitIso R).hom.app M =
      (associatedSheaf R).map (ρ_ ((toPresheaf R).obj M)).hom ≫
        (PresheafOfModules.sheafificationAdjunction
          (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
          (𝟙 _)).counit.app M := rfl
end SheafOfModulesOfCommRing
