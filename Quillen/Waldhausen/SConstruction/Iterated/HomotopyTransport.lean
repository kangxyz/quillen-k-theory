/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Quillen.Topology.Realization.HomotopyNaturality

/-!
The common-universe transport retains every point of the original weak-transformation homotopy and
the actual first spectrum level.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Topology Simplicial
universe u v
namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A))

/-- Universe transport preserves the whole original weak-transformation cylinder. -/
theorem smallModelCylinder_square :
    W.smallModelSSetIso.hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder W.smallModel V.smallModel hF.smallModel hG.smallModel
        (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
        (fun A ↦ hη (AsSmall.down.obj A)) =
      weakNaturalTransformationCylinder W V hF hG η hη ≫ V.smallModelSSetIso.hom := by
  ext n z : 4
  apply Subtype.ext
  change nerveCylinderDiagram
    (whiskerLeft (z.1.val ⋙ AsSmall.up)
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))) z.2.down =
    nerveCylinderDiagram (whiskerLeft z.1.val η) z.2.down ⋙ AsSmall.up
  exact iteratedNerveCylinderDiagram_postcomp (whiskerLeft z.1.val η) AsSmall.up z.2.down

/-- Every point of the actual realization homotopy survives common-universe transport. -/
theorem smallModelRealizationHomotopy (t : unitInterval) (x : W.Delooping) :
    V.smallModelDeloopingHomeomorph
      (weakNaturalTransformationRealizationHomotopy W V hF hG η hη (t,x)) =
      weakNaturalTransformationRealizationHomotopy W.smallModel V.smallModel
        hF.smallModel hG.smallModel
        (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
        (fun A ↦ hη (AsSmall.down.obj A)) (t,W.smallModelDeloopingHomeomorph x) := by
  have hs : W.smallModelSSetIso.hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder W.smallModel V.smallModel hF.smallModel hG.smallModel
        (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
        (fun A ↦ hη (AsSmall.down.obj A)) ≫ V.smallModelSSetIso.inv =
      weakNaturalTransformationCylinder W V hF hG η hη := by
    rw [← Category.assoc, smallModelCylinder_square, Category.assoc,
      Iso.hom_inv_id,Category.comp_id]
  have hh := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy W.smallModel V.smallModel hF.smallModel hG.smallModel
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up)) (fun A ↦ hη (AsSmall.down.obj A)))
    (weakNaturalTransformationHomotopy W V hF hG η hη)
    W.smallModelSSetIso.hom V.smallModelSSetIso.inv hs t x
  apply V.smallModelDeloopingHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact hh.symm

namespace IteratedS
/-- The first spectrum level is precisely the transported original whole homotopy. -/
theorem originalPrespectrumTransformationHomotopy_level_one
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (t : unitInterval) (x : W.Delooping) :
    (originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).level 1
      (t,W.smallModelDeloopingHomeomorph x) =
      V.smallModelDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy W V hF hG η hη (t,x)) := by
  exact (smallModelRealizationHomotopy W V hF hG η hη t x).symm
end IteratedS
end Quillen.Waldhausen
