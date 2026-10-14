/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TensorStalkNaturality
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ScalarExtensionTensor
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.SectionPullbackStalk

/-!
# Natural tensor stalk transport at a genuine geometric section

The coefficient is the actual pullback; the scalar restriction is the actual
projection stalk map, preceded by its canonical point transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Quillen.SchemeSheaf

/-- At a section point, the original tensor with an actual pulled-back coefficient
becomes tensor over the source stalk ring after the original scalar restriction. -/
def sectionPullbackTensorStalkIso {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) (E : X.Modules) :
    moduleTensorLeftFunctor Y ((Scheme.Modules.pullback p).obj E) ⋙ moduleStalk Y (i x) ⋙
        ModuleCat.restrictScalars (sectionStalkRingMap i p h x).hom ≅
      moduleStalk Y (i x) ⋙ ModuleCat.restrictScalars (sectionStalkRingMap i p h x).hom ⋙
        tensorLeft ((moduleStalk X x).obj E) := by
  let α := (sectionStalkRingMap i p h x).hom
  let S := moduleStalk Y (i x)
  let E' := (Scheme.Modules.pullback p).obj E
  let e := (sectionPullbackModuleStalkIso i p h x).app E
  exact Functor.isoWhiskerRight (moduleTensorLeftStalkIso Y (i x) E')
      (ModuleCat.restrictScalars α) ≪≫
    Functor.isoWhiskerLeft S
      (Functor.isoWhiskerRight
          ((curriedTensor (ModuleCat.{u} (Y.presheaf.stalk (i x)))).mapIso e)
          (ModuleCat.restrictScalars α) ≪≫
        scalarExtensionTensorNatIso α ((moduleStalk X x).obj E))

end Quillen.SchemeSheaf
