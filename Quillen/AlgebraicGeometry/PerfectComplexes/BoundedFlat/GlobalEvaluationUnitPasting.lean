/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnit

/-! # Full original unit tracks across global evaluation -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original section identity-action track followed by the actual normalized evaluation. -/
def evaluationOldUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :=
  (prespectrumIsoHomotopy (globalModel.map f.op)
    (onFunctor (globalModel.map f.op).functor
      (globalUnit (Opposite.op X) r))).postcomp
    (prespectrumMap (evaluationModel (Opposite.op X)))

/-- Actual source evaluation followed by the original raw geometric unit homotopy. -/
def evaluationNewUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :=
  Homotopy.precomp (prespectrumMap (evaluationModel (Opposite.op Y)))
    (boundedFlatPerfectUnitHomotopy f r)

/-- The categorical square compares the two original whole unit-track pastings. -/
def evaluationUnitPasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    ((evaluationOldUnit f r).trans
      (evaluationComparison f)).RelHomotopy
    ((evaluationComparison f).trans
      (evaluationNewUnit f r)) := by
  let h := boundedFlatPerfectPullback_exact f
  let J := prespectrumTransformationIntertwiningHomotopy
    (globalModel.map f.op) (evaluationRawMap f)
    (evaluationModel (Opposite.op Y))
    (evaluationModel (Opposite.op X))
    (onFunctor (globalModel.map f.op).functor
      (globalUnit (Opposite.op X) r)).hom
    (evaluationRawUnit f r)
    (evaluationComparisonIso f).hom
    (fun _ ↦ ((globalModel.obj (Opposite.op X)).waldhausen).weq_iso _ inferInstance)
    (fun K ↦ normalizedWeakTransformation_weak h h
      (boundedFlatPerfectPullbackUnitIso f
        r).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
      (AsSmall.down.obj K))
    (fun A ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso f).app A).hom)))
    (evaluation_unit_square f r)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

/-- The actual forward Laurent track is retained literally on the global side. -/
def globalLaurentEvaluationPasting (X : Scheme.{u}ᵒᵖ) :
    (((GlobalSchemeLaurentTrack.homotopy X).postcomp
        (prespectrumMap (evaluationModel
          (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X)))).trans
      (evaluationComparison
        (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop)).RelHomotopy
    ((evaluationComparison
        (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop).trans
      (evaluationNewUnit
        (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop
        (GlobalSchemeLaurentTrack.laurentScalar X))) :=
  evaluationUnitPasting
    (Quillen.KTheory.Bass.GeometricSeedCospan.coefficient.app X).unop
    (GlobalSchemeLaurentTrack.laurentScalar X)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
