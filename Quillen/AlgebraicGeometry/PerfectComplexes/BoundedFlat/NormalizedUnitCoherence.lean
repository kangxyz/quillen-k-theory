/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.UnitCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-! The actual chosen-zero normalized geometric unit and its two unit equations. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The geometric unit with exactly the normalization used by the original map. -/
def boundedFlatNormalizedPullbackIdIso (X : Scheme.{u}) :
    boundedFlatNormalizedPullback (𝟙 X) ≅ 𝟭 (BoundedFlatPerfect X) :=
  (boundedFlatPullbackNormalizationIso (𝟙 X)).symm ≪≫ boundedFlatPerfectPullbackIdIso X

/-- The two transformations in the original identity track compose to this unit. -/
theorem boundedFlatNormalizedPullbackIdIso_hom (X : Scheme.{u}) :
    (boundedFlatNormalizedPullbackIdIso X).hom =
      Waldhausen.normalizedWeakTransformation (boundedFlatPerfectPullback_exact (𝟙 X))
        (Waldhausen.IsExact.id _ _) (boundedFlatPerfectPullbackIdIso X).hom ≫
      (Quillen.rebaseFunctorIso (𝟭 (BoundedFlatPerfect X))
        (boundedFlatPerfectWaldhausen X).zero (boundedFlatPerfectWaldhausen X).zero
        (((Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen X).cof
          (boundedFlatPerfectWaldhausen X).weq).zero (boundedFlatPerfectWaldhausen X).isZero).iso
          (boundedFlatPerfectWaldhausen X).isZero)).inv := by
  simp [boundedFlatNormalizedPullbackIdIso, boundedFlatPullbackNormalizationIso,
    Waldhausen.normalizedWeakTransformation, Category.assoc]

private theorem normalization_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (boundedFlatPullbackNormalizationIso f).inv ≫
      eqToHom (congrArg boundedFlatPerfectPullback e) ≫
      (boundedFlatPullbackNormalizationIso g).hom =
        eqToHom (congrArg boundedFlatNormalizedPullback e) := by
  subst g
  simp

/-- The actual right factor unit survives chosen-zero normalization. -/
theorem boundedFlatNormalizedPullbackCompIso_right_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedPullbackCompIso (𝟙 X) f).hom ≫
      whiskerLeft (boundedFlatNormalizedPullback f) (boundedFlatNormalizedPullbackIdIso X).hom ≫
      (Functor.rightUnitor _).hom =
        eqToHom (congrArg boundedFlatNormalizedPullback (Category.id_comp f)) := by
  apply NatTrans.ext
  funext A
  simp only [boundedFlatNormalizedPullbackCompIso, boundedFlatNormalizedPullbackIdIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, rightUnitor_hom_app,
    Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [(boundedFlatPerfectPullbackIdIso X).hom.naturality_assoc]
  simp only [Functor.id_map]
  have h := congrArg (fun e ↦ e.app A) (boundedFlatPerfectPullbackCompIso_right_unitality f)
  simp only [NatTrans.comp_app, whiskerLeft_app, rightUnitor_hom_app] at h
  erw [Category.comp_id
    ((boundedFlatPerfectPullbackIdIso X).hom.app ((boundedFlatPerfectPullback f).obj A))] at h
  erw [Category.comp_id ((boundedFlatPullbackNormalizationIso f).hom.app A)]
  erw [← Category.assoc _ _ ((boundedFlatPullbackNormalizationIso f).hom.app A), h]
  simpa only [NatTrans.comp_app] using
    congrArg (fun k ↦ k.app A) (normalization_transport (Category.id_comp f))

/-- The actual left factor unit survives chosen-zero normalization. -/
theorem boundedFlatNormalizedPullbackCompIso_left_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedPullbackCompIso f (𝟙 Y)).hom ≫
      whiskerRight (boundedFlatNormalizedPullbackIdIso Y).hom (boundedFlatNormalizedPullback f) ≫
      (Functor.leftUnitor _).hom =
        eqToHom (congrArg boundedFlatNormalizedPullback (Category.comp_id f)) := by
  apply NatTrans.ext
  funext A
  simp only [boundedFlatNormalizedPullbackCompIso, boundedFlatNormalizedPullbackIdIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, leftUnitor_hom_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp]
  rw [← (boundedFlatPullbackNormalizationIso f).hom.naturality_assoc,
    ← (boundedFlatPullbackNormalizationIso f).hom.naturality_assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have h := congrArg (fun e ↦ e.app A) (boundedFlatPerfectPullbackCompIso_left_unitality f)
  simp only [NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app] at h
  erw [Category.comp_id ((boundedFlatPerfectPullback f).map
    ((boundedFlatPerfectPullbackIdIso Y).hom.app A))] at h
  erw [Category.comp_id ((boundedFlatPullbackNormalizationIso f).hom.app A)]
  erw [← Category.assoc _ _ ((boundedFlatPullbackNormalizationIso f).hom.app A), h]
  simpa only [NatTrans.comp_app] using
    congrArg (fun k ↦ k.app A) (normalization_transport (Category.comp_id f))

end Quillen.PerfectComplexes
