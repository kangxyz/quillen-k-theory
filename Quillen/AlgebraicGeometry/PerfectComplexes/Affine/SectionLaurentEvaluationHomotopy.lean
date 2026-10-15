/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentModelUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIntertwiningHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# The original Laurent-unit square across actual section evaluation

The actual categorical unit equation gives the whole relative pasting and moving square.
The section action, original coefficient evaluation track, and normalized raw geometric unit
are unchanged, at all levels and with independent loop, square and structure parameters.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The unchanged section unit has the original model's pointwise weakness. -/
theorem boundedFlatAffineSectionLaurentModelUnit_weak
    (X : (boundedFlatAffineSectionModel R).category) :
    (boundedFlatAffineSectionModel (.of (LaurentPolynomial R))).waldhausen.weq
      ((boundedFlatAffineSectionLaurentModelUnit R).app X) := by
  change (boundedFlatAffineSectionWaldhausen (.of (LaurentPolynomial R))).weq
    ((boundedFlatAffineSectionLaurentPullbackUnitIso R).hom.app X)
  exact (boundedFlatAffineSectionWaldhausen (.of (LaurentPolynomial R))).weq_iso _ inferInstance

/-- The original normalized unit retains pointwise weakness after its actual universe lift. -/
theorem boundedFlatAffineOriginalLaurentModelUnit_weak
    (X : (modelOf (boundedFlatPerfectWaldhausen (Spec R))).category) :
    (modelOf (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))).waldhausen.weq
      ((boundedFlatAffineOriginalLaurentModelUnit R).app X) :=
  normalizedWeakTransformation_weak
    (boundedFlatPerfectPullback_exact (laurentProjection R))
    (boundedFlatPerfectPullback_exact (laurentProjection R))
    (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))).weq_iso _
      inferInstance) (AsSmall.down.obj X)

/-- The complete original strict unit followed by evaluation. -/
def boundedFlatAffineSectionLaurentEvaluationOldUnit :=
  (boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))

/-- The complete original raw geometric unit preceded by evaluation. -/
def boundedFlatAffineSectionLaurentEvaluationNewUnit :=
  Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatLaurentUnitHomotopy R)

/-- The actual unchanged coefficient track intertwines both whole original Laurent actions. -/
def boundedFlatAffineSectionLaurentEvaluationUnitPasting :
    ((boundedFlatAffineSectionLaurentEvaluationOldUnit R).trans
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R))).RelHomotopy
    ((boundedFlatAffineSectionEvaluationCoefficientHomotopy
      (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).trans
        (boundedFlatAffineSectionLaurentEvaluationNewUnit R)) := by
  let J := prespectrumTransformationIntertwiningHomotopy
    (boundedFlatAffineSectionModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R))
    (boundedFlatAffineOriginalCoefficientModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R))
    (boundedFlatAffineSectionEvaluationModelMap R)
    (boundedFlatAffineSectionEvaluationModelMap (.of (LaurentPolynomial R)))
    (boundedFlatAffineSectionLaurentModelUnit R) (boundedFlatAffineOriginalLaurentModelUnit R)
    (boundedFlatAffineSectionEvaluationCoefficientIso
      (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).hom
    (boundedFlatAffineSectionLaurentModelUnit_weak R)
    (boundedFlatAffineOriginalLaurentModelUnit_weak R)
    (fun _ ↦ (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))).smallModel.weq_iso
      _ inferInstance)
    (boundedFlatAffineSectionLaurentModelEvaluationUnitSquare R)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

/-- Actual reverse-track cancellation produces the precise boundary needed by square descent. -/
def boundedFlatAffineSectionLaurentEvaluationUnitBoundary :
    (boundedFlatAffineSectionLaurentEvaluationOldUnit R).RelHomotopy
      (((boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).trans
          (boundedFlatAffineSectionLaurentEvaluationNewUnit R)).trans
        (boundedFlatAffineSectionEvaluationCoefficientHomotopy
          (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).symm) :=
  Homotopy.RelHomotopy.conjugateBoundary _ _ _
    (boundedFlatAffineSectionLaurentEvaluationUnitPasting R)

/-- The original strict/raw Laurent actions have a genuine whole evaluation square. -/
def boundedFlatAffineSectionLaurentEvaluationUnitSquare :
    (boundedFlatAffineSectionLaurentEvaluationOldUnit R).Square
      (boundedFlatAffineSectionLaurentEvaluationNewUnit R)
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R))
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitBoundary R).toSquare

end Quillen.PerfectComplexes
