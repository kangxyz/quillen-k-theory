/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIntertwiningHomotopy

/-! The same original joint unit square as a whole relative comparison of actual tracks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.Scheme.CoefficientBaseChange Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

/-- The original section identity-action track followed by the actual normalized evaluation. -/
def boundedFlatCoefficientSectionEvaluationOldUnit {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :=
  (prespectrumIsoHomotopy (boundedFlatCoefficientSectionModelMap f)
    (onFunctor (boundedFlatCoefficientSectionModelMap f).functor
      (boundedFlatCoefficientSectionUnitIso k r))).postcomp
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap k)

/-- Actual source evaluation followed by the original raw geometric unit homotopy. -/
def boundedFlatCoefficientSectionEvaluationNewUnit {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :=
  Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
    (boundedFlatPerfectUnitHomotopy (Quillen.Scheme.CoefficientBaseChange.map f) r)

/-- The categorical square compares the two original whole unit-track pastings. -/
def boundedFlatCoefficientSectionEvaluationUnitPasting {i k : Index R} (f : i ⟶ k)
    (r : (Γ(space k, ⊤))ˣ) :
    ((boundedFlatCoefficientSectionEvaluationOldUnit f r).trans
      (boundedFlatCoefficientSectionEvaluationHomotopy f)).RelHomotopy
    ((boundedFlatCoefficientSectionEvaluationHomotopy f).trans
      (boundedFlatCoefficientSectionEvaluationNewUnit f r)) := by
  let h := boundedFlatPerfectPullback_exact (Quillen.Scheme.CoefficientBaseChange.map f)
  let J := prespectrumTransformationIntertwiningHomotopy
    (boundedFlatCoefficientSectionModelMap f) (boundedFlatCoefficientOriginalModelMap f)
    (boundedFlatCoefficientSectionEvaluationModelMap i)
    (boundedFlatCoefficientSectionEvaluationModelMap k)
    (onFunctor (boundedFlatCoefficientSectionModelMap f).functor
      (boundedFlatCoefficientSectionUnitIso k r)).hom
    (boundedFlatCoefficientOriginalModelUnit f r)
    (boundedFlatCoefficientSectionEvaluationIso f).hom
    (fun _ ↦ (boundedFlatCoefficientSectionWaldhausen k).weq_iso _ inferInstance)
    (fun X ↦ normalizedWeakTransformation_weak h h
      (boundedFlatPerfectPullbackUnitIso (Quillen.Scheme.CoefficientBaseChange.map f) r).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).weq_iso _ inferInstance)
      (AsSmall.down.obj X))
    (fun _ ↦ (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (boundedFlatCoefficientSectionEvaluation_unit_square f r)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

end Quillen.PerfectComplexes
