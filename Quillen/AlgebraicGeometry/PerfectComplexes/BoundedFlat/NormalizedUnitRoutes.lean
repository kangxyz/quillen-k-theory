/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedUnitTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyPasting

/-! Both normalized geometric unit routes as original prespectrum triangle families. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum (Homotopy)
universe u v
namespace Quillen.Waldhausen.IteratedS

/-- Equality transports of original exact functors preserve every transformation-track value. -/
theorem originalPrespectrumTransformationHomotopy_congr_level
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Waldhausen.Structure C) (V : Waldhausen.Structure D) {F G F' G' : C ⥤ D}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hG : Waldhausen.IsExact W.cof W.weq V.cof V.weq G)
    (hF' : Waldhausen.IsExact W.cof W.weq V.cof V.weq F')
    (hG' : Waldhausen.IsExact W.cof W.weq V.cof V.weq G')
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0F' : F'.obj W.zero = V.zero) (h0G' : G'.obj W.zero = V.zero)
    (eF : F = F') (eG : G = G') (η : F ⟶ G) (η' : F' ⟶ G')
    (hη : ∀ A, V.weq (η.app A)) (hη' : ∀ A, V.weq (η'.app A))
    (he : η ≫ eqToHom eG = eqToHom eF ≫ η') (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).level n =
      (originalPrespectrumTransformationHomotopy W V hF' hG' h0F' h0G' η' hη').level n := by
  subst F'
  subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at he
  subst η'
  rfl

end Quillen.Waldhausen.IteratedS

namespace Quillen.PerfectComplexes

private theorem homotopy_level_transport {X Y : Quillen.LoopPrespectrum}
    {f g g' : X ⟶ Y} (e : g = g')
    (p : Homotopy f g = Homotopy f g') (H : Homotopy f g) (n : ℕ) :
    (p.mp H).level n = H.level n := by
  subst g'
  rfl

/-- Whole values of the normalized composition track before its endpoint-arrow transport. -/
theorem boundedFlatNormalizedCompTrack_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (boundedFlatNormalizedCompTrack f g).level n =
      (originalPrespectrumTransformationHomotopy (boundedFlatPerfectWaldhausen Z)
        (boundedFlatPerfectWaldhausen X) (boundedFlatNormalizedPullback_exact (f ≫ g))
        ((boundedFlatNormalizedPullback_exact g).comp (boundedFlatNormalizedPullback_exact f))
        (boundedFlatNormalizedPullback_obj_zero _)
        ((congrArg (boundedFlatNormalizedPullback f).obj
          (boundedFlatNormalizedPullback_obj_zero g)).trans
          (boundedFlatNormalizedPullback_obj_zero f))
        (boundedFlatNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).level n := by
  unfold boundedFlatNormalizedCompTrack
  apply homotopy_level_transport (originalPrespectrumMap_comp _ _ _
    (boundedFlatNormalizedPullback_exact g) (boundedFlatNormalizedPullback_exact f)
    (boundedFlatNormalizedPullback_obj_zero g) (boundedFlatNormalizedPullback_obj_zero f))

/-- The right unit route keeps the original composition time and unit time. -/
def boundedFlatNormalizedRightUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedFlatPerfectPrespectrumMap f) (boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatNormalizedCompTrack (𝟙 X) f).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.id_comp f)) rfl).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap f)
        (boundedFlatNormalizedIdTrack X)).cast rfl (Category.comp_id _))

/-- The left unit route uses the same original target and the other geometric unit. -/
def boundedFlatNormalizedLeftUnitRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy (boundedFlatPerfectPrespectrumMap f) (boundedFlatPerfectPrespectrumMap f) :=
  ((boundedFlatNormalizedCompTrack f (𝟙 Y)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (Category.comp_id f)) rfl).trans
      (((boundedFlatNormalizedIdTrack Y).postcomp
        (boundedFlatPerfectPrespectrumMap f)).cast rfl (Category.id_comp _))

/-- The actual first component of the right unit triangle, with its scheme transport. -/
def boundedFlatNormalizedRightUnitFirst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatNormalizedPullback f ≅
      boundedFlatNormalizedPullback f ⋙ boundedFlatNormalizedPullback (𝟙 X) :=
  eqToIso (congrArg boundedFlatNormalizedPullback (Category.id_comp f).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso (𝟙 X) f

/-- The actual second component of the right unit triangle. -/
def boundedFlatNormalizedRightUnitSecond {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatNormalizedPullback f ⋙ boundedFlatNormalizedPullback (𝟙 X) ≅
      boundedFlatNormalizedPullback f :=
  isoWhiskerLeft (boundedFlatNormalizedPullback f) (boundedFlatNormalizedPullbackIdIso X) ≪≫
    Functor.rightUnitor _

/-- The actual first component of the left unit triangle, with its scheme transport. -/
def boundedFlatNormalizedLeftUnitFirst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatNormalizedPullback f ≅
      boundedFlatNormalizedPullback (𝟙 Y) ⋙ boundedFlatNormalizedPullback f :=
  eqToIso (congrArg boundedFlatNormalizedPullback (Category.comp_id f).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso f (𝟙 Y)

/-- The actual second component of the left unit triangle. -/
def boundedFlatNormalizedLeftUnitSecond {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatNormalizedPullback (𝟙 Y) ⋙ boundedFlatNormalizedPullback f ≅
      boundedFlatNormalizedPullback f :=
  isoWhiskerRight (boundedFlatNormalizedPullbackIdIso Y) (boundedFlatNormalizedPullback f) ≪≫
    Functor.leftUnitor _

/-- Both original normalized unit triangles have the same actual composite transformation. -/
theorem boundedFlatNormalizedUnitRoutes_equation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedRightUnitFirst f).hom ≫
      (boundedFlatNormalizedRightUnitSecond f).hom =
        (boundedFlatNormalizedLeftUnitFirst f).hom ≫
          (boundedFlatNormalizedLeftUnitSecond f).hom := by
  simp only [boundedFlatNormalizedRightUnitFirst, boundedFlatNormalizedRightUnitSecond,
    boundedFlatNormalizedLeftUnitFirst, boundedFlatNormalizedLeftUnitSecond,
    Iso.trans_hom, eqToIso.hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc]
  rw [boundedFlatNormalizedPullbackCompIso_right_unitality,
    boundedFlatNormalizedPullbackCompIso_left_unitality]

/-- The two entire normalized unit routes compare by their actual original weak triangles. -/
def boundedFlatNormalizedUnitRoutesComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatNormalizedRightUnitRoute f).RelHomotopy
      (boundedFlatNormalizedLeftUnitRoute f) := by
  let W := boundedFlatPerfectWaldhausen Y
  let U := boundedFlatPerfectWaldhausen X
  let hf := boundedFlatNormalizedPullback_exact f
  let hx := boundedFlatNormalizedPullback_exact (𝟙 X)
  let hy := boundedFlatNormalizedPullback_exact (𝟙 Y)
  have J := originalPrespectrumPastingHomotopy W U hf (hf.comp hx) (hy.comp hf) hf
    (boundedFlatNormalizedPullback_obj_zero f)
    ((congrArg (boundedFlatNormalizedPullback (𝟙 X)).obj
      (boundedFlatNormalizedPullback_obj_zero f)).trans
        (boundedFlatNormalizedPullback_obj_zero (𝟙 X)))
    ((congrArg (boundedFlatNormalizedPullback f).obj
      (boundedFlatNormalizedPullback_obj_zero (𝟙 Y))).trans
        (boundedFlatNormalizedPullback_obj_zero f))
    (boundedFlatNormalizedPullback_obj_zero f)
    (boundedFlatNormalizedRightUnitFirst f).hom (boundedFlatNormalizedRightUnitSecond f).hom
    (boundedFlatNormalizedLeftUnitFirst f).hom (boundedFlatNormalizedLeftUnitSecond f).hom
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (boundedFlatNormalizedUnitRoutes_equation f)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rw [Homotopy.cast_level, boundedFlatNormalizedCompTrack_level]
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _
        (congrArg boundedFlatNormalizedPullback (Category.id_comp f)) rfl
      simp [boundedFlatNormalizedRightUnitFirst]
    · have h := originalPrespectrumTransformationHomotopy_precomp_level hf hx
        (Waldhausen.IsExact.id U.cof U.weq)
        (boundedFlatNormalizedPullback_obj_zero f)
        (boundedFlatNormalizedPullback_obj_zero (𝟙 X)) rfl
        (boundedFlatNormalizedPullbackIdIso X).hom
        (fun _ ↦ U.weq_iso _ inferInstance) n
      refine h.symm.trans ?_
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _ rfl rfl
      apply NatTrans.ext
      funext A
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
        boundedFlatNormalizedRightUnitSecond, Iso.trans_hom, isoWhiskerLeft_hom,
        NatTrans.comp_app, rightUnitor_hom_app]
      exact (Category.comp_id _).symm
  · intro n
    apply Homotopy.trans_level_congr
    · rw [Homotopy.cast_level, boundedFlatNormalizedCompTrack_level]
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _
        (congrArg boundedFlatNormalizedPullback (Category.comp_id f)) rfl
      simp [boundedFlatNormalizedLeftUnitFirst]
    · have h := originalPrespectrumTransformationHomotopy_postcomp_level hy
        (Waldhausen.IsExact.id W.cof W.weq) hf
        (boundedFlatNormalizedPullback_obj_zero (𝟙 Y)) rfl
        (boundedFlatNormalizedPullback_obj_zero f)
        (boundedFlatNormalizedPullbackIdIso Y).hom
        (fun _ ↦ W.weq_iso _ inferInstance) n
      refine h.symm.trans ?_
      apply originalPrespectrumTransformationHomotopy_congr_level
        W U _ _ _ _ _ _ _ _ rfl rfl
      apply NatTrans.ext
      funext A
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
        boundedFlatNormalizedLeftUnitSecond, Iso.trans_hom, isoWhiskerRight_hom,
        NatTrans.comp_app, leftUnitor_hom_app]
      exact (Category.comp_id _).symm

end Quillen.PerfectComplexes
