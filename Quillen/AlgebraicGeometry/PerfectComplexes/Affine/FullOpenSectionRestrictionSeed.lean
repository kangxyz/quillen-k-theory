/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenUnit
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeed

/-!
# Original Laurent-track and Bass-seed compatibility of full-open restriction

The original section restriction and its literal evaluation square preserve the supplied
ambient unit and its actual restriction to the open. The compatible-action predicates share
the same categorical types and retain every forward component. The actual Model diagram
square then preserves the entire original Laurent track. Its unchanged four-corner map and
original source-leg null cylinder give the actual Bass-seed equation. The localization null
is not substituted for that Bass cylinder, and no unit or seed premise is supplied.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair Quillen.FunctorIdentityAutomorphism
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u v w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original faithful evaluation square transfers matching original actions to restriction. -/
theorem boundedFlatAffineFullOpenSectionRestriction_evaluation_preserves (a : Under R) :
    EvaluationPreserves (boundedFlatAffineFullOpenSectionRestriction j a)
      (boundedFlatAffineFullOpenOriginalEvaluation j a)
      (boundedFlatAffineSectionFullOpenRestriction j a) :=
  evaluationPreserves_of_eq (boundedFlatAffineFullOpenSectionRestriction j a)
    (boundedFlatAffineFullOpenOriginalEvaluation j a)
    (boundedFlatAffineSectionFullOpenRestriction j a)
    (boundedFlatAffineFullOpenSectionRestriction_comp_evaluation j a)

omit [IsOpenImmersion j] in
/-- Original source evaluation followed by open pullback retains the prescribed forward unit. -/
theorem boundedFlatAffineSectionFullOpenRestriction_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatAffineSectionFullOpenRestriction j a)
      (boundedFlatAffineSectionUnitIso a.right r)
      (boundedFlatPerfectGlobalUnitIso (openSpace j a) (boundedFlatAffineFullOpenUnit j a r)) :=
  fun S => boundedFlatAffineSectionFullOpenRestriction_unit j a r S

/-- Original full-open evaluation retains the same actual restricted target unit. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatAffineFullOpenOriginalEvaluation j a)
      (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r))
      (boundedFlatPerfectGlobalUnitIso (openSpace j a) (boundedFlatAffineFullOpenUnit j a r)) :=
  fun S => boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom j a
    (boundedFlatAffineFullOpenUnit j a r) S

/-- The actual section restriction preserves every component of the original forward unit. -/
theorem boundedFlatAffineFullOpenSectionRestriction_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatAffineFullOpenSectionRestriction j a)
      (boundedFlatAffineSectionUnitIso a.right r)
      (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r)) :=
  boundedFlatAffineFullOpenSectionRestriction_evaluation_preserves j a
    (boundedFlatAffineSectionUnitIso a.right r)
    (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r))
    (boundedFlatPerfectGlobalUnitIso (openSpace j a) (boundedFlatAffineFullOpenUnit j a r))
    (boundedFlatAffineSectionFullOpenRestriction_unit_preserves j a r)
    (boundedFlatAffineFullOpenOriginalEvaluation_unit_preserves j a r)

/-- Shared Model endpoints keep the action-preservation input folded during realization. -/
private theorem identityActionTrack_square_apply {C D E H : Model.{u}}
    (F : C ⟶ D) (G : E ⟶ H) (a : C ⟶ E) (b : D ⟶ H)
    (α : 𝟭 D ≅ 𝟭 D) (β : 𝟭 H ≅ 𝟭 H) (h : F ≫ b = a ≫ G)
    (hunit : Preserves b.functor α β) (n : ℕ) (t : unitInterval)
    (x : (prespectrum C).space n) :
    (prespectrumMap b).map n
        ((prespectrumIsoHomotopy F (onFunctor F.functor α)).level n (t, x)) =
      (prespectrumIsoHomotopy G (onFunctor G.functor β)).level n
        (t, (prespectrumMap a).map n x) :=
  prespectrumIsoHomotopy_square_apply F G a b (onFunctor F.functor α)
    (onFunctor G.functor β) h
    (onFunctor_whisker_square F.functor G.functor a.functor b.functor
      (eqToHom (congrArg Model.Hom.functor h)) α β hunit.whisker) n t x

/-- Restriction preserves the unchanged original coordinate unit on its Laurent coefficient. -/
private theorem restrictionLaurentUnitPreserves (a : Under R) :
    Preserves
      (boundedFlatAffineSectionFullOpenModelMap j ((laurentUnderFunctor R).obj a)).functor
      (boundedFlatAffineSectionLaurentUnitIso a.right)
      (boundedFlatAffineFullOpenSectionLaurentUnitIso j a) :=
  boundedFlatAffineFullOpenSectionRestriction_unit_preserves j
    ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right)

/-- Diagram endpoints share their types before specialization to geometric coefficients. -/
private theorem identityActionDiagramTrack_square_apply {I : Type v} [Category.{w} I]
    (C D : I ⥤ Model.{u}) (r : C ⟶ D) {a b : I} (f : a ⟶ b)
    (α : 𝟭 (C.obj b) ≅ 𝟭 (C.obj b)) (β : 𝟭 (D.obj b) ≅ 𝟭 (D.obj b))
    (hunit : Preserves (r.app b).functor α β) (n : ℕ) (t : unitInterval)
    (x : (prespectrum (C.obj a)).space n) :
    (prespectrumMap (r.app b)).map n
        ((prespectrumIsoHomotopy (C.map f) (onFunctor (C.map f).functor α)).level n (t, x)) =
      (prespectrumIsoHomotopy (D.map f) (onFunctor (D.map f).functor β)).level n
        (t, (prespectrumMap (r.app a)).map n x) :=
  identityActionTrack_square_apply (C.map f) (D.map f) (r.app a) (r.app b)
    α β (r.naturality f) hunit n t x

/-- The original restriction preserves the entire Laurent track at the identical time. -/
theorem boundedFlatAffineSectionFullOpenLaurentHomotopy_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app
        ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n
        (t, ((boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a).map n x) :=
  identityActionDiagramTrack_square_apply
    (boundedFlatAffineSectionOpenModelFunctor j)
    (boundedFlatAffineFullOpenSectionModelFunctor j)
    (boundedFlatAffineSectionFullOpenModelTransformation j)
    ((laurentUnderCoefficient R).app a)
    (boundedFlatAffineSectionLaurentUnitIso a.right)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)
    (restrictionLaurentUnitPreserves j a) n t x

/-- The original whole Laurent time slice commutes with the same restriction components. -/
theorem boundedFlatAffineSectionFullOpenLaurentHomotopy_at (a : Under R) (t : unitInterval) :
    (boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).at t ≫
        (boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app
          ((laurentUnderFunctor R).obj a) =
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a ≫
        (boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).at t := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact boundedFlatAffineSectionFullOpenLaurentHomotopy_apply j a n t x

/-- The original four restriction components give the actual Laurent-square map. -/
def boundedFlatAffineSectionFullOpenBassSquareMap (a : Under R) :
    boundedFlatAffineSectionOpenBassSquare j a ⟶
      boundedFlatAffineFullOpenSectionBassSquare j a :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u + 1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u + 1}).map
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The actual cone functor acts on the unchanged four-corner restriction map. -/
def boundedFlatAffineSectionFullOpenBassConeMap (a : Under R) :
    boundedFlatAffineSectionOpenBassCone j a ⟶
      boundedFlatAffineFullOpenSectionBassCone j a :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineSectionFullOpenBassSquareMap j a))

/-- The original source-leg null cylinder survives at the identical interval value. -/
theorem boundedFlatAffineSectionFullOpenBassNullHomotopy_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSectionFullOpenBassConeMap j a).map n
        ((boundedFlatAffineSectionOpenBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenSectionBassNullHomotopy j a).level n
        (t, ((boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineSectionFullOpenBassSquareMap j a) n t x

/-- Both constructed seed maps commute with the original restriction of sections. -/
theorem boundedFlatAffineSectionFullOpenBassSeedMap_square (a : Under R) :
    boundedFlatAffineSectionOpenBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineSectionFullOpenBassConeMap j a) =
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a ≫
        boundedFlatAffineFullOpenSectionBassSeedMap j a := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a))).map n
        (((boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app
          ((laurentUnderFunctor R).obj a)).map n
          ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenSectionBassSquare j a))).map n
          ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n
            (t, ((boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a).map n x))
    rw [boundedFlatAffineSectionFullOpenLaurentHomotopy_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSectionFullOpenBassNullHomotopy_apply j a n t x

section
attribute [local irreducible] boundedFlatAffineSectionOpenPrespectrumFunctor
  boundedFlatAffineFullOpenSectionPrespectrumFunctor
  boundedFlatAffineSectionFullOpenPrespectrumTransformation

/-- The unchanged Bass functor acts by the same original looped restriction cone map. -/
theorem boundedFlatAffineSectionFullOpenBassFunctor_app (a : Under R) :
    ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)).app a =
      parameterLoopingMap (boundedFlatAffineSectionFullOpenBassConeMap j a) := rfl

end

attribute [local irreducible] boundedFlatAffineSectionOpenPrespectrumFunctor
  boundedFlatAffineFullOpenSectionPrespectrumFunctor
  boundedFlatAffineFullOpenSectionBassSeed boundedFlatAffineSectionOpenBassSeed
  boundedFlatAffineSectionFullOpenPrespectrumTransformation

/-- The actual coefficient-natural restriction preserves the unchanged original Bass seeds. -/
theorem boundedFlatAffineSectionFullOpenBassSeed_restriction :
    boundedFlatAffineSectionOpenBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSectionFullOpenPrespectrumTransformation j) =
      boundedFlatAffineSectionFullOpenPrespectrumTransformation j ≫
        boundedFlatAffineFullOpenSectionBassSeed j := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, boundedFlatAffineFullOpenSectionBassSeed_app,
    boundedFlatAffineSectionFullOpenBassFunctor_app,
    boundedFlatAffineSectionOpenBassSeed_app]
  exact boundedFlatAffineSectionFullOpenBassSeedMap_square j a

end Quillen.PerfectComplexes
