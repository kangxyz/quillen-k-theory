/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberLocalizationModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientRestriction

/-! # The three original G7 coefficient rows and the actual support inclusion square -/
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

private theorem reflectInclusion {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) (F G : C ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hF : P.lift (F ⋙ P.ι) (fun X => (F.obj X).property) = F := rfl
  have hG : P.lift (G ⋙ P.ι) (fun X => (G.obj X).property) = G := rfl
  rw [← hF, ← hG]
  exact supported_lift_congr P h _ _

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original fiber reindexing retains its literal full-subcategory inclusion. -/
theorem fineFiberMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedFlatCoefficientSupportedFiberModelMap f T g).functor ⋙
        (boundedFlatCoefficientSectionSupported
          (boundedFlatCoefficientFiberSupportOpen f T b).ι).ι =
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι ⋙
        ((boundedFlatCoefficientSectionModelRow Q).map g).functor := rfl

/-- The actual original fiber comparison is coefficient-natural before evaluation. -/
theorem fiberComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g) ≫ fiberComponent f T b =
      fiberComponent f T a ≫ (boundedFlatCoefficientSupportedFiberModelFunctor f T).map g := by
  apply Model.Hom.ext
  apply reflectInclusion
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T b).ι)
  have hs := congrArg Model.Hom.functor
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).naturality (specUnder.map g))
  have hr := congrArg Model.Hom.functor ((parameterCoefficientRestriction Q).naturality g)
  change ((ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g)).functor ⋙
      ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj b)).functor =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).functor ⋙
      ((ParameterModels.ambient Q.left).map (specUnder.map g)).functor at hs
  change ((ParameterModels.ambient Q.left).map (specUnder.map g)).functor ⋙
      ((parameterCoefficientRestriction Q).app b).functor =
    ((parameterCoefficientRestriction Q).app a).functor ⋙
      ((boundedFlatCoefficientSectionModelRow Q).map g).functor at hr
  change ((ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g)).functor ⋙
      (fiberComponent f T b).functor ⋙
        (boundedFlatCoefficientSectionSupported
          (boundedFlatCoefficientFiberSupportOpen f T b).ι).ι =
    (fiberComponent f T a).functor ⋙
      (boundedFlatCoefficientSupportedFiberModelMap f T g).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T b).ι).ι
  rw [fiberComponent_forget, fineFiberMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← fiberComponent_forget]
  rfl

/-- The full original fiber row comparison, retaining the old G7 model diagram. -/
def fiberComparison :
    specUnder ⋙ ParameterAuxiliarySupport.fiber f.left T ⟶
      boundedFlatCoefficientSupportedFiberModelFunctor f T where
  app := fiberComponent f T
  naturality _ _ g := fiberComponent_naturality f T g

omit [IsOpenImmersion f.left] in
/-- Original full-open reindexing retains its literal full-subcategory inclusion. -/
theorem fineOpenMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedFlatCoefficientSupportedFullOpenModelMap f T g).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T b).ι).ι =
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι ⋙
        ((boundedFlatCoefficientSectionModelRow P).map g).functor := rfl

omit [IsOpenImmersion f.left] in
/-- The actual original full-open comparison is coefficient-natural before evaluation. -/
theorem openComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g) ≫ openComponent f T b =
      openComponent f T a ≫ (boundedFlatCoefficientSupportedFullOpenModelFunctor f T).map g := by
  apply Model.Hom.ext
  apply reflectInclusion
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T b).ι)
  have hs := congrArg Model.Hom.functor
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).naturality (specUnder.map g))
  have hr := congrArg Model.Hom.functor ((parameterCoefficientRestriction P).naturality g)
  change ((ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g)).functor ⋙
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj b)).functor =
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).functor ⋙
      ((ParameterModels.ambient P.left).map (specUnder.map g)).functor at hs
  change ((ParameterModels.ambient P.left).map (specUnder.map g)).functor ⋙
      ((parameterCoefficientRestriction P).app b).functor =
    ((parameterCoefficientRestriction P).app a).functor ⋙
      ((boundedFlatCoefficientSectionModelRow P).map g).functor at hr
  change ((ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g)).functor ⋙
      (openComponent f T b).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T b).ι).ι =
    (openComponent f T a).functor ⋙
      (boundedFlatCoefficientSupportedFullOpenModelMap f T g).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T b).ι).ι
  rw [openComponent_forget, fineOpenMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← openComponent_forget]
  rfl

/-- The full original supported-open row comparison, with its actual native target. -/
def openComparison :
    specUnder ⋙ ParameterAuxiliarySupport.openModel f.left T ⟶
      boundedFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := openComponent f T
  naturality _ _ g := openComponent_naturality f T g

/-- The original support enlargement square commutes as complete Model transformations. -/
theorem enlargement_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.enlargement f.left T) ≫
        ambientComparison Q T =
      fiberComparison f T ≫ boundedFlatCoefficientSupportedFiberForgetModelTransformation f T := by
  apply NatTrans.ext
  funext a
  apply Model.Hom.ext
  apply reflectInclusion
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι)
  have he := congrArg (fun η => (η.app (specUnder.obj a)).functor)
    (ParameterAuxiliarySupport.enlargement_forget f.left T)
  change ((ParameterAuxiliarySupport.enlargement f.left T).app (specUnder.obj a)).functor ⋙
      ((ParameterModels.forget T.ι).app (specUnder.obj a)).functor =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).functor at he
  change ((ParameterAuxiliarySupport.enlargement f.left T).app (specUnder.obj a)).functor ⋙
      (ambientComponent Q T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).ι =
    (fiberComponent f T a).functor ⋙
      (boundedFlatCoefficientSupportedFiberForgetModelMap f T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).ι
  rw [ambientComponent_forget, ← Functor.assoc, he]
  change _ = (fiberComponent f T a).functor ⋙
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι
  exact (fiberComponent_forget f T a).symm

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
