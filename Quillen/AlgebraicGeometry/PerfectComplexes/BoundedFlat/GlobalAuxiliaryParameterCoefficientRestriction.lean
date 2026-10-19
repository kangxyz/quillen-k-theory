/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientDiagrams

/-! # The original auxiliary supported full-open restriction square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The ambient pair map is the original full-open map with its actual weak-change factor. -/
theorem ambientMap_eq_fullRestriction :
    ParameterAuxiliarySupport.ambientMap f.left =
      GlobalParameterCoefficient.parameterFullRestriction f := by
  apply NatTrans.ext
  funext a
  apply Model.Hom.ext
  rfl

omit [IsOpenImmersion f.left] in
/-- The original joint section restriction square holds before realization. -/
theorem originalRestriction_square :
    globalOpenFineRestriction f ≫ rowRestriction P =
      rowRestriction Q ≫ boundedFlatCoefficientSectionModelRestriction f := by
  apply NatTrans.ext
  funext a
  exact (coefficientRestriction _).naturality
    (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a))

/-- The actual parameter comparison commutes with full ambient restriction. -/
theorem ambientRestriction_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.ambientMap f.left) ≫
        parameterCoefficientRestriction P =
      parameterCoefficientRestriction Q ≫ boundedFlatCoefficientSectionModelRestriction f := by
  rw [ambientMap_eq_fullRestriction]
  unfold parameterCoefficientRestriction
  rw [← Category.assoc, GlobalParameterCoefficient.fullRestriction_model_square,
    Category.assoc, originalRestriction_square, ← Category.assoc]

private theorem reflectInclusion {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) (F G : C ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hF : P.lift (F ⋙ P.ι) (fun X => (F.obj X).property) = F := rfl
  have hG : P.lift (G ⋙ P.ι) (fun X => (G.obj X).property) = G := rfl
  rw [← hF, ← hG]
  exact supported_lift_congr P h _ _

omit [IsOpenImmersion f.left] in
/-- The actual old supported full restriction retains its original ambient section map. -/
theorem fineRestriction_forget (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a) ≫
        boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a).functor ⋙
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι =
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).ι ⋙
      ((boundedFlatCoefficientSectionModelRestriction f).app a).functor := rfl

/-- The complete supported restriction square preserves the original G7 fine/coarse/full factor. -/
theorem restriction_square (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.restriction f.left T) ≫
        openComparison f T =
      ambientComparison Q T ≫
        (boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
          boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T) := by
  apply NatTrans.ext
  funext a
  apply Model.Hom.ext
  apply reflectInclusion
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι)
  have hs := congrArg (fun η => (η.app (specUnder.obj a)).functor)
    (ParameterAuxiliarySupport.restriction_forget f.left T)
  change ((ParameterAuxiliarySupport.restriction f.left T).app (specUnder.obj a)).functor ⋙
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).functor =
    ((ParameterModels.forget T.ι).app (specUnder.obj a)).functor ⋙
      ((ParameterAuxiliarySupport.ambientMap f.left).app (specUnder.obj a)).functor at hs
  have hr := congrArg (fun η => (η.app a).functor) (ambientRestriction_square f)
  change ((ParameterAuxiliarySupport.ambientMap f.left).app (specUnder.obj a)).functor ⋙
      ((parameterCoefficientRestriction P).app a).functor =
    ((parameterCoefficientRestriction Q).app a).functor ⋙
      ((boundedFlatCoefficientSectionModelRestriction f).app a).functor at hr
  change ((ParameterAuxiliarySupport.restriction f.left T).app (specUnder.obj a)).functor ⋙
      (openComponent f T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι =
    (ambientComponent Q T a).functor ⋙
      ((boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a) ≫
        boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι
  rw [openComponent_forget, fineRestriction_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← ambientComponent_forget]
  rfl

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
