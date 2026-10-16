/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackCoherence
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationPasting

/-! The actual canonical normalization of geometric pullback retains its original associativity. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The exact chosen-zero normalization used by the original bounded-flat prespectrum map. -/
def boundedFlatNormalizedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X :=
  Quillen.rebaseFunctor (boundedFlatPerfectPullback f)
    (boundedFlatPerfectWaldhausen Y).zero (boundedFlatPerfectWaldhausen X).zero
    (((boundedFlatPerfectPullback_exact f).zero (boundedFlatPerfectWaldhausen Y).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)

/-- The actual normalized pullback remains exact for the original Waldhausen structures. -/
theorem boundedFlatNormalizedPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen Y).cof
      (boundedFlatPerfectWaldhausen Y).weq (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq (boundedFlatNormalizedPullback f) :=
  (boundedFlatPerfectPullback_exact f).rebase

/-- Canonical normalization preserves the exact chosen zero on the nose. -/
@[simp] theorem boundedFlatNormalizedPullback_obj_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedPullback f).obj (boundedFlatPerfectWaldhausen Y).zero =
      (boundedFlatPerfectWaldhausen X).zero :=
  Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The unchanged canonical isomorphism from original to normalized geometric pullback. -/
def boundedFlatPullbackNormalizationIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatPerfectPullback f ≅ boundedFlatNormalizedPullback f :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The actual geometric composition iso followed by the original binary normalizations. -/
def boundedFlatNormalizedPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFlatNormalizedPullback (f ≫ g) ≅
      boundedFlatNormalizedPullback g ⋙ boundedFlatNormalizedPullback f :=
  (boundedFlatPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedFlatPerfectPullbackCompIso f g ≪≫
    isoWhiskerRight (boundedFlatPullbackNormalizationIso g) (boundedFlatPerfectPullback f) ≪≫
    isoWhiskerLeft _ (boundedFlatPullbackNormalizationIso f)

/-- This is precisely the composite of the two original transformations in the geometric
prespectrum composition track, with the intermediate normalization canceled. -/
theorem boundedFlatNormalizedPullbackCompIso_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedFlatNormalizedPullbackCompIso f g).hom =
      Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact (f ≫ g))
        ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
        (boundedFlatPerfectPullbackCompIso f g).hom ≫
      (exactNormalizationCompIso (boundedFlatPerfectPullback_exact g)
        (boundedFlatPerfectPullback_exact f)).hom := by
  simp [boundedFlatNormalizedPullbackCompIso, boundedFlatPullbackNormalizationIso,
    Waldhausen.normalizedWeakTransformation, exactNormalizationCompIso, Category.assoc]
  rfl

/-- Both genuine three-map geometric comparison routes remain equal after the exact original
normalizations; the scheme associativity transport and functor associator are explicit. -/
theorem boundedFlatNormalizedPullbackCompIso_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedFlatNormalizedPullbackCompIso f (g ≫ h)).hom ≫
      whiskerRight (boundedFlatNormalizedPullbackCompIso g h).hom
        (boundedFlatNormalizedPullback f) ≫
      (Functor.associator (boundedFlatNormalizedPullback h) (boundedFlatNormalizedPullback g)
        (boundedFlatNormalizedPullback f)).hom =
    eqToHom (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≫
      (boundedFlatNormalizedPullbackCompIso (f ≫ g) h).hom ≫
      whiskerLeft (boundedFlatNormalizedPullback h)
        (boundedFlatNormalizedPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext A
  simp only [comp_obj, boundedFlatNormalizedPullbackCompIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_comp, whiskerRight_twice,
    Category.assoc, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Functor.comp_map, associator_inv_app, Category.comp_id,
    Category.id_comp, ← map_comp, NatTrans.naturality, NatTrans.naturality_assoc,
    Iso.hom_inv_id_app_assoc, eqToHom_refl, whiskerLeft_comp, whiskerLeft_twice]
  rw [Functor.map_comp,
    ← (boundedFlatPullbackNormalizationIso f).hom.naturality_assoc]
  have hc := congrArg (fun e ↦ e.app A) (boundedFlatPerfectPullbackCompIso_two_routes f g h)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id,
    eqToHom_refl, Category.id_comp] at hc
  rw [← Category.assoc ( (boundedFlatPerfectPullbackCompIso f (g ≫ h)).hom.app A)
    ((boundedFlatPerfectPullback f).map ((boundedFlatPerfectPullbackCompIso g h).hom.app A))]
  rw [hc]
  simp only [Category.assoc]
  rfl

/-- The two total normalized geometric triple-pullback routes have an actual relative
prespectrum comparison, directly from the genuine geometric equation. This compares their
original transformation tracks; splitting them into the existing binary tracks is separate. -/
def boundedFlatNormalizedTriplePasting {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  originalPrespectrumPastingHomotopy (boundedFlatPerfectWaldhausen T)
    (boundedFlatPerfectWaldhausen X)
    (boundedFlatNormalizedPullback_exact (f ≫ g ≫ h))
    ((boundedFlatNormalizedPullback_exact (g ≫ h)).comp (boundedFlatNormalizedPullback_exact f))
    ((boundedFlatNormalizedPullback_exact h).comp (boundedFlatNormalizedPullback_exact (f ≫ g)))
    ((boundedFlatNormalizedPullback_exact h).comp
      ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f)))
    (boundedFlatNormalizedPullback_obj_zero _)
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])
    (by simp only [comp_obj, boundedFlatNormalizedPullback_obj_zero])
    (boundedFlatNormalizedPullbackCompIso f (g ≫ h)).hom
    (whiskerRight (boundedFlatNormalizedPullbackCompIso g h).hom
      (boundedFlatNormalizedPullback f) ≫
      (Functor.associator (boundedFlatNormalizedPullback h) (boundedFlatNormalizedPullback g)
        (boundedFlatNormalizedPullback f)).hom)
    (eqToHom (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≫
      (boundedFlatNormalizedPullbackCompIso (f ≫ g) h).hom)
    (whiskerLeft (boundedFlatNormalizedPullback h)
      (boundedFlatNormalizedPullbackCompIso f g).hom)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (by simpa only [Category.assoc] using boundedFlatNormalizedPullbackCompIso_two_routes f g h)

end Quillen.PerfectComplexes
