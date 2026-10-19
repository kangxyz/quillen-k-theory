/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientModels

/-! # Whole coefficient naturality of the original auxiliary support comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex

private theorem subcategoryFunctor_ext {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) (F G : C ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hF : P.lift (F ⋙ P.ι) (fun X => (F.obj X).property) = F := rfl
  have hG : P.lift (G ⋙ P.ι) (fun X => (G.obj X).property) = G := rfl
  rw [← hF, ← hG]
  exact supported_lift_congr P h _ _

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- Forgetting auxiliary support gives the exact original ambient coefficient comparison. -/
theorem ambientComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).ι =
      ((ParameterModels.forget T.ι).app (specUnder.obj a)).functor ⋙
        ((parameterCoefficientRestriction Q).app a).functor := by
  have hr : ((parameterCoefficientRestriction Q).app a).functor =
      (globalModel.map (canonicalRowIso Q a).hom.op ≫ (rowRestriction Q).app a).functor := by
    unfold parameterCoefficientRestriction
    rw [NatTrans.comp_app, parameterRowModelIso_hom_app]
  rw [hr]
  have hp := supportedPairReindex_forget (parameterSupportPairIso Q T a).hom
  dsimp only [supportOpenPair] at hp
  rw [parameterSupportPairIso_hom_right] at hp
  exact congrArg (fun F => F ⋙ ((coefficientRestriction _).app (op Q, a)).functor) hp

/-- Original auxiliary-supported coefficient reindexing retains its full-subcategory inclusion. -/
theorem fineAmbientMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedFlatCoefficientSupportedAmbientModelMap T g).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T b).ι).ι =
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).ι ⋙
        ((boundedFlatCoefficientSectionModelRow Q).map g).functor := rfl

/-- The actual component comparison is natural for every original coefficient morphism. -/
theorem ambientComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.ambient T).map (specUnder.map g) ≫ ambientComponent Q T b =
      ambientComponent Q T a ≫ (boundedFlatCoefficientSupportedAmbientModelFunctor T).map g := by
  apply Model.Hom.ext
  apply subcategoryFunctor_ext
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T b).ι)
  have hs := congrArg Model.Hom.functor ((ParameterModels.forget T.ι).naturality (specUnder.map g))
  have hr := congrArg Model.Hom.functor ((parameterCoefficientRestriction Q).naturality g)
  change ((ParameterAuxiliarySupport.ambient T).map (specUnder.map g)).functor ⋙
      ((ParameterModels.forget T.ι).app (specUnder.obj b)).functor =
    ((ParameterModels.forget T.ι).app (specUnder.obj a)).functor ⋙
      ((ParameterModels.ambient Q.left).map (specUnder.map g)).functor at hs
  change ((ParameterModels.ambient Q.left).map (specUnder.map g)).functor ⋙
      ((parameterCoefficientRestriction Q).app b).functor =
    ((parameterCoefficientRestriction Q).app a).functor ⋙
      ((boundedFlatCoefficientSectionModelRow Q).map g).functor at hr
  change ((ParameterAuxiliarySupport.ambient T).map (specUnder.map g)).functor ⋙
      (ambientComponent Q T b).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T b).ι).ι =
    (ambientComponent Q T a).functor ⋙
      (boundedFlatCoefficientSupportedAmbientModelMap T g).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T b).ι).ι
  rw [ambientComponent_forget, fineAmbientMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc,
    ← ambientComponent_forget]
  rfl

/-- The complete parameter auxiliary support row maps to the unchanged original G7 ambient row. -/
def ambientComparison :
    specUnder ⋙ ParameterAuxiliarySupport.ambient T ⟶
      boundedFlatCoefficientSupportedAmbientModelFunctor T where
  app := ambientComponent Q T
  naturality _ _ g := ambientComponent_naturality Q T g

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
