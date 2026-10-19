/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedRawPullbackTrack
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackCoherence

/-!
# Original supported pullback associativity

The two complete supported geometric composition routes agree by faithful support-forgetting
and the already proved original ambient pullback equation. The original functor associator and
geometric composition transport are retained. No relative filler is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass

/-- Forgetting support retains the original ambient pullback object. -/
private theorem pullback_forget_obj {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B)
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).obj
        ((boundedFlatPerfectSupportedPullback f).obj K) =
      (boundedFlatPerfectPullback f.hom.right).obj
        ((tensorCoefficientSupportedForget B.obj.hom).obj K) := rfl

/-- The full supported geometric triple routes agree under their original associativity
transport, proved through the faithful inclusion into the ambient bounded-flat category. -/
theorem pullbackCompIso_two_routes {A B C D : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (boundedFlatPerfectSupportedPullbackCompIso f (g ≫ h)).hom ≫
      whiskerRight (boundedFlatPerfectSupportedPullbackCompIso g h).hom
        (boundedFlatPerfectSupportedPullback f) ≫
      (Functor.associator (boundedFlatPerfectSupportedPullback h)
        (boundedFlatPerfectSupportedPullback g) (boundedFlatPerfectSupportedPullback f)).hom =
    eqToHom (congrArg boundedFlatPerfectSupportedPullback (Category.assoc f g h).symm) ≫
      (boundedFlatPerfectSupportedPullbackCompIso (f ≫ g) h).hom ≫
      whiskerLeft (boundedFlatPerfectSupportedPullback h)
        (boundedFlatPerfectSupportedPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  let : (tensorCoefficientSupportedForget A.obj.hom).Faithful := by
    unfold tensorCoefficientSupportedForget
    infer_instance
  apply (tensorCoefficientSupportedForget A.obj.hom).map_injective
  simpa only [NatTrans.comp_app, Functor.map_comp, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.comp_id, Category.id_comp, Functor.map_id,
    eqToHom_app, eqToHom_map, eqToHom_refl,
    boundedFlatPerfectSupportedPullbackCompIso_forget_hom_app,
    boundedFlatPerfectSupportedPullback_forget_map, Functor.comp_obj,
    pullback_forget_obj, ObjectProperty.FullSubcategory.comp_hom, Arrow.comp_right] using
    congrArg (fun η => η.app ((tensorCoefficientSupportedForget D.obj.hom).obj K))
      (boundedFlatPerfectPullbackCompIso_two_routes f.hom.right g.hom.right h.hom.right)

end Quillen.PerfectComplexes.GlobalSupportedRawBass
