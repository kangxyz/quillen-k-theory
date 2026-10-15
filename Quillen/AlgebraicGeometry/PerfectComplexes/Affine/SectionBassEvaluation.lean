/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationBoundary
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopySquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep

/-!
# The actual one-step Bass evaluation map

The proved original geometric boundary descends to the literal two comparison maps and then
to their original cones. Compatibility with the original Laurent-unit seed requires its
additional unit/null comparison and is not asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- Original evaluation maps the whole strict polynomial span to the raw geometric span. -/
def boundedFlatAffineSectionBassSpanEvaluation :
    StrictSquare.span (boundedFlatAffineSectionBassSquare R) ⟶
      HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) :=
  HomotopyPushout.mapOfHomotopies
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))

/-- Original source-cylinder endpoints regroup for literal quotient descent. -/
def boundedFlatAffineSectionBassEvaluationSourceDescTrack :=
  (boundedFlatAffineSectionBassEvaluationSourceTrack R).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Original target-cylinder endpoints regroup for the same quotient descent. -/
def boundedFlatAffineSectionBassEvaluationTargetDescTrack :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)) ≫
          boundedFlatPerfectPrespectrumMap (laurentPlus R)))
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)) ≫
          boundedFlatPerfectPrespectrumMap (laurentMinus R))) :=
  (boundedFlatAffineSectionBassEvaluationTargetTrack R).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The original Laurent boundaries are precomposed by the literal strict source legs. -/
def boundedFlatAffineSectionBassEvaluationPastedDescTrack :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        (boundedFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom Polynomial.toLaurent) ≫
            boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))))
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        (boundedFlatAffineSectionPrespectrumFunctor.map
          (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) ≫
            boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))) :=
  ((Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom Polynomial.toLaurent))).trans
      (boundedFlatAffineSectionBassEvaluationTargetDescTrack R)).trans
    (Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)))).symm

/-- The proved original geometric boundary supplies the exact moving-descent interface. -/
def boundedFlatAffineSectionBassEvaluationDescPasting :
    (boundedFlatAffineSectionBassEvaluationSourceDescTrack R).RelHomotopy
      (boundedFlatAffineSectionBassEvaluationPastedDescTrack R) :=
  (boundedFlatAffineSectionBassEvaluationPasting R).ofLevels _ _ (fun _ => rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · rfl)

/-- The target cylinder is the original span-map cylinder followed by original raw Bass. -/
theorem boundedFlatAffineSectionBassEvaluationTargetDescTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationTargetDescTrack R).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatAffineSectionEvaluationPrespectrumMap R)
        (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
        (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)))
        (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))
        (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))).postcomp
          (boundedFlatBassSquareComparison R)).level n := by
  simp only [boundedFlatAffineSectionBassEvaluationTargetDescTrack, Homotopy.cast_level,
    boundedFlatAffineSectionBassEvaluationTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · rfl
    · exact congrArg (fun H => H.level n)
        (Homotopy.postcomp_symm
          (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R))
          (boundedFlatPerfectPrespectrumMap (laurentMinus R))).symm

/-- Source descent is the original strict comparison followed by unchanged Laurent evaluation. -/
theorem boundedFlatAffineSectionBassEvaluationSourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
      (boundedFlatAffineSectionPrespectrumFunctor.map (CommRingCat.ofHom Polynomial.toLaurent) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedFlatAffineSectionPrespectrumFunctor.map
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) ≫
          boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedFlatAffineSectionBassEvaluationSourceDescTrack R) =
    StrictSquare.comparison (boundedFlatAffineSectionBassSquare R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- Target descent is the actual original span evaluation followed by raw Bass comparison. -/
theorem boundedFlatAffineSectionBassEvaluationTargetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
      (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
      (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R))
      (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus R))
      (boundedFlatAffineSectionBassEvaluationTargetDescTrack R) =
    boundedFlatAffineSectionBassSpanEvaluation R ≫ boundedFlatBassSquareComparison R := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedFlatAffineSectionBassEvaluationTargetDescTrack_level R n)
      (s, x)

/-- The proved whole geometric filler descends to the two unchanged comparison-map composites. -/
def boundedFlatAffineSectionBassComparisonEvaluationHomotopy :
    Homotopy (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedFlatAffineSectionBassSpanEvaluation R ≫ boundedFlatBassSquareComparison R) :=
  (HomotopyPushout.descSquareHomotopy
    (H₀ := boundedFlatAffineSectionBassEvaluationSourceDescTrack R)
    (H₁ := boundedFlatAffineSectionBassEvaluationTargetDescTrack R)
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom Polynomial.toLaurent))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy
      (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)))
    (boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare).cast
      (boundedFlatAffineSectionBassEvaluationSourceDesc_eq R)
      (boundedFlatAffineSectionBassEvaluationTargetDesc_eq R)

/-- Every positive endpoint retains the complete original positive evaluation homotopy. -/
theorem boundedFlatAffineSectionBassComparisonEvaluationHomotopy_inl (n : ℕ)
    (r : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inl
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))).map n x) =
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom Polynomial.toLaurent)).level n (r, x) := rfl

/-- The independent inverse-coordinate endpoint keeps its distinct original evaluation track. -/
theorem boundedFlatAffineSectionBassComparisonEvaluationHomotopy_inr (n : ℕ)
    (r : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj (.of (Polynomial R))).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, (HomotopyPushout.inr
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))).map n x) =
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := .of (Polynomial R)) (S := .of (LaurentPolynomial R))
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))).level n
          (r, x) := rfl

/-- The complete original double cylinder is the proved moving geometric evaluation square. -/
theorem boundedFlatAffineSectionBassComparisonEvaluationHomotopy_cylinder (n : ℕ)
    (r s : unitInterval) (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R)) n (s, x)) =
      (boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare.level n (r, (s, x)) := rfl

/-- Original evaluation and its proved comparison square map the literal Bass cones. -/
def boundedFlatAffineSectionBassConeEvaluation :
    boundedFlatAffineSectionBassCone R ⟶ mappingCone (boundedFlatBassSquareComparison R) :=
  mappingConeSquareMap (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R))
    (boundedFlatBassSquareComparison R) (boundedFlatAffineSectionBassSpanEvaluation R)
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R)

/-- Laurent evaluation remains literal on the original cone inclusion. -/
theorem boundedFlatAffineSectionBassConeEvaluation_inclusion :
    mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)) ≫
        boundedFlatAffineSectionBassConeEvaluation R =
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison R) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- Parameter looping yields the actual one-step evaluation map on the original Bass objects. -/
def boundedFlatAffineSectionBassStepEvaluation :
    (boundedFlatAffineSectionBassDiagram 1).obj R ⟶ boundedFlatAffineBassStep R :=
  parameterLoopingMap (boundedFlatAffineSectionBassConeEvaluation R)

end Quillen.PerfectComplexes
