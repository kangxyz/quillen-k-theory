/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionCoefficientComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting

/-!
# The original Laurent-chart evaluation pasting

The two actual Laurent inclusions specialize the proved evaluation composition coherence.
All original coefficient homotopies and geometric composition tracks are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- A Laurent chart uses its original split geometric composition homotopy. -/
def boundedFlatAffineSectionChartGeometricTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (Spec.map k)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (Spec.map k) (polynomialProjection R)).cast
    (congrArg boundedFlatPerfectPrespectrumMap
      ((Spec.map_comp (coefficient R) k).symm.trans (congrArg Spec.map h))) rfl

/-- Original evaluation followed by the actual chart composition track. -/
def boundedFlatAffineSectionChartOuterTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map k)) :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy (laurentCoefficient R)).trans
    ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatAffineSectionChartGeometricTrack R k h)).cast rfl
        (Category.assoc _ _ _).symm)

/-- The same original chart route formed by the two coefficient evaluation tracks. -/
def boundedFlatAffineSectionChartWhiskeredTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map k)) :=
  (boundedFlatAffineSectionCoefficientWhiskeredRoute (coefficient R) k).cast
    (congrArg (fun f => boundedFlatAffineSectionPrespectrumFunctor.map f ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))) h) rfl

/-- The actual chart coefficient equation identifies the full outer Laurent track. -/
def boundedFlatAffineSectionChartEvaluationPasting (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    (boundedFlatAffineSectionChartWhiskeredTrack R k h).RelHomotopy
      (boundedFlatAffineSectionChartOuterTrack R k h) := by
  apply (boundedFlatAffineSectionCoefficientCompositionRelHomotopy (coefficient R) k).symm.ofLevels
  · intro n
    rfl
  · intro n
    apply Homotopy.trans_level_congr
    · have level_congr {A B : CommRingCat.{u}} {f g : A ⟶ B} (e : f = g) :
          (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n =
            (boundedFlatAffineSectionEvaluationCoefficientHomotopy g).level n := by
        subst e
        rfl
      exact (level_congr h).symm
    · rfl

/-- The first whiskered coefficient track, transported by the actual strict chart equation. -/
def boundedFlatAffineSectionChartFirstTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map k)) :=
  (Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy k)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
        ((boundedFlatAffineSectionPrespectrumFunctor.map_comp (coefficient R) k).symm.trans
          (congrArg boundedFlatAffineSectionPrespectrumFunctor.map h))))
    (Category.assoc _ _ _).symm

/-- Strict chart endpoint transport changes no value of the original precomposed track. -/
theorem boundedFlatAffineSectionChartFirstTrack_level (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) (n : ℕ) :
    (boundedFlatAffineSectionChartFirstTrack R k h).level n =
      (Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionEvaluationCoefficientHomotopy k)).level n := rfl

/-- The original chart evaluation track on the literal uncollapsed strict source leg. -/
def boundedFlatAffineSectionChartMovingTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R)) :=
  (Homotopy.precomp (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy k)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- Collapsing only the strict chart equation retains every original moving-track value. -/
theorem boundedFlatAffineSectionChartMovingTrack_level (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) (n : ℕ) :
    (boundedFlatAffineSectionChartMovingTrack R k).level n =
      (boundedFlatAffineSectionChartFirstTrack R k h).level n := by
  exact (Homotopy.cast_level _ _ _ n).trans
    (boundedFlatAffineSectionChartFirstTrack_level R k h n).symm

/-- The second coefficient track retains original geometric postcomposition. -/
def boundedFlatAffineSectionChartSecondTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R)) :
    Homotopy
      ((boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map k))
      ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
          boundedFlatPerfectPrespectrumMap (Spec.map k)) :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R)).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map k))

/-- The actual two coefficient tracks form the proved chart evaluation pasting. -/
def boundedFlatAffineSectionChartFirstPasting (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : coefficient R ≫ k = laurentCoefficient R) :
    ((boundedFlatAffineSectionChartFirstTrack R k h).trans
      (boundedFlatAffineSectionChartSecondTrack R k)).RelHomotopy
        (boundedFlatAffineSectionChartOuterTrack R k h) := by
  apply (boundedFlatAffineSectionCoefficientCompositionRelHomotopy (coefficient R) k).symm.ofLevels
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · have level_congr {A B : CommRingCat.{u}} {f g : A ⟶ B} (e : f = g) :
          (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n =
            (boundedFlatAffineSectionEvaluationCoefficientHomotopy g).level n := by
        subst e
        rfl
      exact (level_congr h).symm
    · rfl

/-- The genuine positive Laurent chart supplies its exact evaluation pasting. -/
def boundedFlatAffineSectionPlusEvaluationPasting (R : CommRingCat.{u}) :=
  boundedFlatAffineSectionChartEvaluationPasting R (CommRingCat.ofHom Polynomial.toLaurent)
    (coefficient_toLaurent R)

/-- The separate inverse-coordinate Laurent chart supplies its exact evaluation pasting. -/
def boundedFlatAffineSectionMinusEvaluationPasting (R : CommRingCat.{u}) :=
  boundedFlatAffineSectionChartEvaluationPasting R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
    (coefficient_toLaurent_invert R)

/-- The positive geometric chart track is exactly the previously constructed original track. -/
theorem boundedFlatAffineSectionChartGeometricTrack_plus (R : CommRingCat.{u}) :
    boundedFlatAffineSectionChartGeometricTrack R (CommRingCat.ofHom Polynomial.toLaurent)
      (coefficient_toLaurent R) =
        boundedFlatLaurentPlusHomotopy R := rfl

/-- The negative geometric track retains the original inverse-coordinate leg and its timing. -/
theorem boundedFlatAffineSectionChartGeometricTrack_minus (R : CommRingCat.{u}) :
    boundedFlatAffineSectionChartGeometricTrack R
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
      (coefficient_toLaurent_invert R) =
        boundedFlatLaurentMinusHomotopy R := rfl

end Quillen.PerfectComplexes
