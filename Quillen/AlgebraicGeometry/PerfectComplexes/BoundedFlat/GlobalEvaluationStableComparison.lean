/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientKStableComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-!
# The original global evaluation and stable K-groups

Actual normalized evaluation from the global bounded-flat section Model is a
stable equivalence. Its original geometric comparison homotopies make the
localized evaluations natural on all schemes. The inverse of this unchanged
evaluation identifies every original nonnegative K-group with the stable group
of the global Model diagram. The representative equation retains the actual
evaluation map. No compactness or quasi-separatedness hypothesis is needed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.CategoryTheory.GrothendieckSections Quillen.CategoryTheory.GrothendieckZeroSections
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Original global evaluation, followed by the actual common-universe equivalence. -/
def evaluationSmallEquivalence (X : Scheme.{u}ᵒᵖ) :
    globalModel.obj X ≌ SmallModel (BoundedFlatPerfect X.unop) :=
  (originalEvaluationEquivalence boundedFlatPerfectPseudofunctor X).trans AsSmall.equiv

/-- The actual inverse lowers the universe and uses the original evaluation inverse. -/
theorem evaluationSmallEquivalence_inverse_exact (X : Scheme.{u}ᵒᵖ) :
    IsExact (boundedFlatPerfectWaldhausen X.unop).smallModel.cof
      (boundedFlatPerfectWaldhausen X.unop).smallModel.weq
      (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (evaluationSmallEquivalence X).inverse :=
  (boundedFlatPerfectWaldhausen X.unop).smallModel_down_exact.comp
    (Structure.ofEquivalence_inverse_exact _ _ _ (fiberZero_isZero X))

/-- The genuine equivalence retains the already chosen normalized evaluation functor. -/
def evaluationModelEquivalence (X : Scheme.{u}ᵒᵖ) :
    globalModel.obj X ≌ modelOf (boundedFlatPerfectWaldhausen X.unop) :=
  (evaluationSmallEquivalence X).changeFunctor (evaluationNormalizationIso X)

/-- The original normalized evaluation has an actual exact categorical inverse. -/
theorem evaluationModel_isStableEquivalence (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (prespectrumMap (evaluationModel X)) :=
  ExactModelEquivalence.isStableEquivalence (evaluationModelEquivalence X)
    (evaluationModel X).exact (evaluationSmallEquivalence_inverse_exact X)
    (evaluationModel X).zero

/-- Actual normalized evaluation is inverted in the existing stable localization. -/
def evaluationLocalizedIso (X : Scheme.{u}ᵒᵖ) :
    (globalModel ⋙ prespectrumFunctor ⋙ toStableLocalization).obj X ≅
      BoundedFlatLocalizedSpectrumFunctor.obj X :=
  stableLocalizationIso (prespectrumMap (evaluationModel X))
    (evaluationModel_isStableEquivalence X)

/-- The forward localized map is precisely the original normalized evaluation. -/
@[simp] theorem evaluationLocalizedIso_hom (X : Scheme.{u}ᵒᵖ) :
    (evaluationLocalizedIso X).hom =
      toStableLocalization.map (prespectrumMap (evaluationModel X)) := rfl

/-- The actual geometric evaluation comparison gives every localized naturality square. -/
theorem evaluationLocalizedIso_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (globalModel ⋙ prespectrumFunctor ⋙ toStableLocalization).map f ≫
        (evaluationLocalizedIso Y).hom =
      (evaluationLocalizedIso X).hom ≫ BoundedFlatLocalizedSpectrumFunctor.map f := by
  change toStableLocalization.map (prespectrumMap (globalModel.map f)) ≫
      toStableLocalization.map (prespectrumMap (evaluationModel Y)) =
    toStableLocalization.map (prespectrumMap (evaluationModel X)) ≫
      toStableLocalization.map (prespectrumMap (evaluationRawMap f.unop))
  have h := toStableLocalization_map_eq_of_homotopy (evaluationComparison f.unop)
  simpa only [Functor.map_comp, Opposite.op_unop, Quiver.Hom.op_unop] using h

/-- Original global evaluation is a natural localized equivalence on all schemes. -/
def evaluationLocalizedNatIso :
    globalModel.{u} ⋙ prespectrumFunctor ⋙ toStableLocalization ≅
      BoundedFlatLocalizedSpectrumFunctor :=
  NatIso.ofComponents evaluationLocalizedIso (fun f => evaluationLocalizedIso_naturality f)

/-- The inverse of actual evaluation identifies the original nonnegative K-functor. -/
def globalKStableNatIso (n : ℕ) :
    boundedFlatPerfectKAddFunctor.{u} n ≅
      globalModel ⋙ prespectrumFunctor ⋙ stableHomotopyFunctor (n : ℤ) :=
  boundedFlatPerfectKLocalizedStableNatIso n ≪≫
    (isoWhiskerRight evaluationLocalizedNatIso (localizedStableHomotopyFunctor (n : ℤ))).symm

/-- Composing with actual normalized evaluation recovers the original K/stable comparison. -/
@[reassoc]
theorem globalKStableNatIso_evaluation (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (globalKStableNatIso n).hom.app X ≫
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (evaluationModel X)) =
      (originalKStableEquiv (boundedFlatPerfectWaldhausen X.unop) n).toAddCommGrpIso.hom := by
  let A := boundedFlatPerfectKLocalizedStableNatIso n
  let E := isoWhiskerRight evaluationLocalizedNatIso (localizedStableHomotopyFunctor (n : ℤ))
  have hE : E.hom.app X = (stableHomotopyFunctor (n : ℤ)).map
      (prespectrumMap (evaluationModel X)) := rfl
  change (A.hom.app X ≫ E.inv.app X) ≫ _ = _
  rw [← hE, Category.assoc, ← NatTrans.comp_app, E.inv_hom_id, NatTrans.id_app]
  exact Category.comp_id (A.hom.app X)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
