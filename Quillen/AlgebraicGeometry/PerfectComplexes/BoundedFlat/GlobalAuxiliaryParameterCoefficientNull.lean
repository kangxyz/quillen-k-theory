/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLocalizationNull

/-! # The original G7 auxiliary null under actual integral Spec-row comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex

private theorem zero_postcomp {V W U : Model.{u}} (J : W ⟶ U) :
    zeroHom V U = zeroHom V W ≫ J := by
  simpa only [Category.id_comp] using (zeroHom_square (𝟙 V) J).symm

private def zeroPostcomp {V W U : Model.{u}} (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).functor ⟶ F.functor) :
    (zeroHom V U).functor ⟶ (F ≫ J).functor :=
  eqToHom (congrArg Model.Hom.functor (zero_postcomp J)) ≫ Functor.whiskerRight η J.functor

private theorem zeroPostcomp_weak {V W U : Model.{u}} (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) (X : V) :
    U.waldhausen.weq ((zeroPostcomp F J η).app X) := by
  apply U.waldhausen.weq.comp_mem
  · exact U.waldhausen.weq_iso _ (by infer_instance)
  · exact J.exact.weak _ (hη X)

private theorem zeroPostcomp_level {V W U : Model.{u}} (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X)) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := zeroHom V U) (G := F ≫ J)
      (zeroPostcomp F J η)
      (zeroPostcomp_weak F J η hη)).level n =
      ((prespectrumTransformationHomotopy (F := zeroHom V W) (G := F) η hη).postcomp
        (prespectrumMap J)).level n :=
  (prespectrumTransformationHomotopy_source_transport_level
    (F := zeroHom V U) (F' := zeroHom V W ≫ J) (G := F ≫ J) (zero_postcomp J)
    (Functor.whiskerRight η J.functor) (fun X => J.exact.weak _ (hη X))
    (zeroPostcomp_weak F J η hη) n).trans
      (prespectrumTransformationHomotopy_postcomp_level (F := zeroHom V W) (G := F) η hη J n)

private theorem fullNull_postcomp_naturality {V W U V' W' T' U' : Model.{u}}
    (f : V ⟶ W) (g : W ⟶ U)
    (f' : V' ⟶ W') (g' : W' ⟶ T') (J' : T' ⟶ U')
    (a : V ⟶ V') (b : U ⟶ U')
    (h : (f ≫ g) ≫ b = a ≫ ((f' ≫ g') ≫ J'))
    (η : (zeroHom V U).functor ⟶ (f ≫ g).functor)
    (η' : (zeroHom V' T').functor ⟶ (f' ≫ g').functor)
    (hη : ∀ X, U.waldhausen.weq (η.app X))
    (hη' : ∀ X, T'.waldhausen.weq (η'.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n
      ((prespectrumCompositeZeroNullHomotopy f g η hη).level n (s, x)) =
    (prespectrumMap J').map n
      ((prespectrumCompositeZeroNullHomotopy f' g' η' hη').level n
        (s, (prespectrumMap a).map n x)) := by
  have hn := prespectrumZeroTransformationHomotopy_naturality
    (f ≫ g) ((f' ≫ g') ≫ J') a b h η (zeroPostcomp (f' ≫ g') J' η')
    hη (zeroPostcomp_weak (f' ≫ g') J' η' hη') n
  have hv := congrArg (fun H => H (unitInterval.symm s, x)) hn
  change (prespectrumMap b).map n
    ((prespectrumTransformationHomotopy _ _).level n (unitInterval.symm s, x)) =
      (prespectrumTransformationHomotopy _ _).level n
        (unitInterval.symm s, (prespectrumMap a).map n x) at hv
  rw [zeroPostcomp_level] at hv
  exact hv

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Both actual supported arrows give the original complete G7 composite Model square. -/
theorem fullComposite_model_square :
    (Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.enlargement f.left T) ≫
      Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.restriction f.left T)) ≫
        openComparison f T =
      fiberComparison f T ≫
        ((boundedFlatCoefficientSupportedFiberForgetModelTransformation f T ≫
          boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T) ≫
          boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T) := by
  rw [Category.assoc, restriction_square, ← Category.assoc, enlargement_square,
    Category.assoc, Category.assoc]

/-- Every original reversed null time agrees with the G7 coarse null after full restriction. -/
theorem fullNull_coefficient_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterAuxiliarySupport.fiber f.left T).obj
      (specUnder.obj a))).space n) :
    (prespectrumMap ((openComparison f T).app a)).map n
      (((ParameterAuxiliarySupport.fullNull f.left T).homotopy (specUnder.obj a)).level n
        (s, x)) =
      (prespectrumMap (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a)).map n
        (((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n
          (s, (prespectrumMap ((fiberComparison f T).app a)).map n x)) := by
  apply fullNull_postcomp_naturality
    ((ParameterAuxiliarySupport.enlargement f.left T).app (specUnder.obj a))
    ((ParameterAuxiliarySupport.restriction f.left T).app (specUnder.obj a))
    ((boundedFlatCoefficientSupportedFiberForgetModelTransformation f T).app a)
    (boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a)
    (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a)
    ((fiberComparison f T).app a) ((openComparison f T).app a)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation,
    boundedFlatCoefficientSupportedOpenRestrictionModelTransformation,
    boundedFlatCoefficientSupportedFullOpenModelFunctor] using
    congrArg (fun k => k.app a) (fullComposite_model_square f T)

/-- Each original auxiliary null time is an actual scheme-natural transformation. -/
def parameterNullTimeSlice (s : unitInterval) :
    ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor ⟶
      ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor :=
  diagramHomotopyAt
    (η := Functor.whiskerRight (ParameterAuxiliarySupport.enlargement f.left T)
      prespectrumFunctor ≫ Functor.whiskerRight (ParameterAuxiliarySupport.restriction f.left T)
        prespectrumFunctor)
    (θ := diagramZeroMap (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
      (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor))
    (ParameterAuxiliarySupport.fullNull f.left T).homotopy
    (ParameterAuxiliarySupport.fullNull f.left T).naturality s

/-- The same original G7 coarse-null time, followed by its actual full restriction. -/
def coefficientFullNullTimeSlice (s : unitInterval) :
    boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T :=
  diagramHomotopyAt
    (η := boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T)
      (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T))
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).naturality s ≫
      boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T

/-- The full same-time comparison is a strict square of original natural transformations. -/
theorem fullNull_timeSlice_square (s : unitInterval) :
    Functor.whiskerLeft specUnder (parameterNullTimeSlice f T s) ≫
        Functor.whiskerRight (openComparison f T) prespectrumFunctor =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        coefficientFullNullTimeSlice f T s := by
  apply NatTrans.ext
  funext a
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact fullNull_coefficient_square f T a n s x

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
