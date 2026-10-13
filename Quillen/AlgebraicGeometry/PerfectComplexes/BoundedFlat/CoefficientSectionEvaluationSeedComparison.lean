/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationTopology
public import Quillen.Topology.Prespectrum.ConeSquareLevelWeakEquivalence
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# The original fine-to-raw native Bass cone and seed comparison

The cone map descends the proved whole comparison square. Its positive source-null boundary
uses the unchanged source leg and original geometric composition track. The resulting relative
comparison combines with the original Laurent unit pasting to compare the actual one-step
seeds, preserving the independent comparison, loop and structure coordinates.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The original whole evaluation square descends to the actual fine and raw quotient cones. -/
def boundedFlatCoefficientFullOpenBassConeEvaluation (a : Under R) :
    boundedFlatCoefficientFullOpenBassCone f a ⟶
      mappingCone (boundedFlatCoefficientBassSquareComparison P a) :=
  mappingConeSquareMap
    (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
    (boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy f a)

/-- Evaluation commutes literally on the original Laurent inclusion. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_inclusion (a : Under R) :
    mappingConeInclusion (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a)) ≫
        boundedFlatCoefficientFullOpenBassConeEvaluation f a =
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) :=
  mappingConeSquareMap_inclusion ..

/-- The whole original cone cylinder first follows Hc, then the raw cone contraction. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_cylinder
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a)).space n) :
    (boundedFlatCoefficientFullOpenBassConeEvaluation f a).map n
      ((mappingConeHomotopy
        (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))).level n (s, x)) =
      (((boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy f a).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
          (Homotopy.precomp (boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
            (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)))).level n
              (s, x) := rfl

/-- The first half retains the independent whole comparison time. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_first_half
    (a : Under R) (n : ℕ) (r : unitInterval)
    (x : (StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a)).space n) :
    (boundedFlatCoefficientFullOpenBassConeEvaluation f a).map n
      ((mappingConeHomotopy
        (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))).level n
          (⟨(r : ℝ) / 2, by constructor <;> linarith [r.2.1, r.2.2]⟩, x)) =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n
        ((boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy f a).level n (r, x)) :=
  mappingConeSquareMap_first_half ..

/-- The second half retains the original raw cone coordinate and the actual span evaluation. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_second_half
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a)).space n) :
    (boundedFlatCoefficientFullOpenBassConeEvaluation f a).map n
      ((mappingConeHomotopy
        (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))).level n
          (⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, x)) =
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level n
        (s, (boundedFlatCoefficientFullOpenBassSpanEvaluation f a).map n x) :=
  mappingConeSquareMap_second_half ..

/-- The actual whole-square cone evaluation is completely weak at each original level. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_level_isWeakHomotopyEquivalence
    (a : Under R) (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatCoefficientFullOpenBassConeEvaluation f a).map n) :=
  mappingConeSquareMap_level_isWeakHomotopyEquivalence _ _ _ _ _ n
    (boundedFlatCoefficientFullOpenBassSpan_point_homotopyExtensionProperty f a n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (laurentUnderFunctor R).obj a) n)
    (boundedFlatCoefficientBassSpan_point_homotopyExtensionProperty P a n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))) n)
    (boundedFlatCoefficientFullOpenBassSpanEvaluation_level_isWeakHomotopyEquivalence f a n)
    (boundedFlatCoefficientSectionEvaluation_level_isWeakHomotopyEquivalence
      (op P, (laurentUnderFunctor R).obj a) n)

/-- The same actual cone map is stable, as a consequence of its complete levelwise weakness. -/
theorem boundedFlatCoefficientFullOpenBassConeEvaluation_isStableEquivalence (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientFullOpenBassConeEvaluation f a) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatCoefficientFullOpenBassConeEvaluation_level_isWeakHomotopyEquivalence f a)

/-- The original fine positive source null, postcomposed with the actual cone evaluation. -/
def boundedFlatCoefficientFullOpenBassEvaluationOldNull (a : Under R) :
    Homotopy (((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
      ((laurentUnderCoefficient R).app a) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap
          (op P, (laurentUnderFunctor R).obj a)) ≫
          mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (zeroHom ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  ((boundedFlatCoefficientFullOpenBassNullHomotopy f a).postcomp
    (boundedFlatCoefficientFullOpenBassConeEvaluation f a)).cast
      rfl
      (by apply Hom.ext; funext n; ext x
          exact (boundedFlatCoefficientFullOpenBassConeEvaluation f a).map_point n)

/-- The original raw positive source null, precomposed with original base evaluation. -/
def boundedFlatCoefficientFullOpenBassEvaluationNewNull (a : Under R) :=
  Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientBassLaurentNullHomotopy P a)

namespace CoefficientSectionEvaluationSeedComparison

/-- The original source-leg/cone boundary with its terminal constant edge removed relatively. -/
def sourceLegConePasting (a : Under R) :
    (Homotopy.precomp
      (StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a) ≫
        boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a))).RelHomotopy
    (((boundedFlatCoefficientFullOpenBassSourceLegEvaluationHomotopy f a).postcomp
      (boundedFlatCoefficientBassSquareComparison P a ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
      (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
        boundedFlatCoefficientBassSourceLeg P a)
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)))) := by
  let J := boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeBoundary f a
  have hz : ((boundedFlatCoefficientFullOpenBassSourceLegEvaluationHomotopy f a).postcomp
      (zeroHom _ (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))).symm =
      Quillen.LoopPrespectrum.Homotopy.refl (Quillen.LoopPrespectrum.zeroHom _ _) := by
    apply Quillen.LoopPrespectrum.Homotopy.ext
    rfl
  rw [hz] at J
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

end CoefficientSectionEvaluationSeedComparison

namespace CoefficientSectionEvaluationSeedComparison

/-- The cone source-leg cylinder uses the proved positive inclusion face of Hc. -/
theorem originalOldNull_level (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a).level n =
    (((boundedFlatCoefficientFullOpenChartFirstTrack f a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
      (Homotopy.precomp
        (StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a) ≫
          boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)))).level n := by
  let leg := StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a)
  let inc := mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)
  let H := boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy f a
  let N := mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)
  let V := boundedFlatCoefficientFullOpenBassSpanEvaluation f a
  have hC : (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a).level n =
      (Homotopy.precomp leg ((H.postcomp inc).trans (Homotopy.precomp V N))).level n := by
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact boundedFlatCoefficientFullOpenBassConeEvaluation_cylinder f a n s (leg.map n x)
  rw [hC, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact congrArg (inc.map n)
      (boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy_inl f a n s
        (((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
          ((polynomialUnderCoefficient R).app a)).map n x))
  · rfl

end CoefficientSectionEvaluationSeedComparison

namespace CoefficientSectionEvaluationSeedComparison

/-- The unchanged old source-leg cone track, with its positive-chart endpoint displayed. -/
def oldConeLegNull (a : Under R) :
    Homotopy
      ((((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
          ((polynomialUnderCoefficient R).app a) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap
          (op P, (polynomialUnderFunctor R).obj a)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (zeroHom ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  (Homotopy.precomp
    (StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a) ≫
      boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a))).cast rfl rfl

/-- The unchanged evaluated raw source-leg cone track at its positive-chart endpoint. -/
def newConeLegNull (a : Under R) :
    Homotopy
      (((boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
        boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (zeroHom ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
    boundedFlatCoefficientBassSourceLeg P a)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a))).cast rfl rfl

/-- The original source-leg boundary gives the positive-chart cone pasting. -/
def positiveConePasting (a : Under R) :
    (oldConeLegNull f a).RelHomotopy
      (((boundedFlatCoefficientFullOpenChartSecondTrack f a ((underToLaurent R).app a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
          (newConeLegNull f a)) :=
  (sourceLegConePasting f a).ofLevels _ _
    (by intro n; rfl) (by intro n; apply Homotopy.trans_level_congr <;> rfl)

/-- The positive geometric specialization retains the original split native composition track. -/
theorem originalPositiveTrack_level (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a)).level n =
      (boundedFlatCoefficientLaurentPlusHomotopy P a).level n := rfl

/-- The original outer positive boundary has precisely Laurent movement followed by split track. -/
theorem positiveOuterTrack_level (a : Under R) (n : ℕ) :
    ((boundedFlatCoefficientFullOpenChartOuterTrack f a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).level n =
    ((boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a).trans
      ((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
        (boundedFlatCoefficientLaurentPlusHomotopy P a)).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))).level n := by
  let inc := mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)
  let L := boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
    (𝟙 (op P), (laurentUnderCoefficient R).app a)
  let T := (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a))).cast rfl (Category.assoc _ _ _).symm
  have hp := congrArg (fun H => H.level n) (Homotopy.postcomp_trans L T inc)
  refine hp.trans (Homotopy.trans_level_congr _ _ _ _ n rfl ?_)
  apply Homotopy.postcomp_level_congr
  change (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a))).level n = _
  exact Homotopy.precomp_level_congr _ _ _ n (originalPositiveTrack_level (P := P) a n)

/-- Positive native composition gives the unchanged Laurent movement and original split track. -/
def positiveChartPasting (a : Under R) :
    (((boundedFlatCoefficientFullOpenChartFirstTrack f a ((underToLaurent R).app a)
      (polynomialUnderCoefficient_toLaurent R a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
      ((boundedFlatCoefficientFullOpenChartSecondTrack f a ((underToLaurent R).app a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))).RelHomotopy
    ((boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a).trans
      ((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
        (boundedFlatCoefficientLaurentPlusHomotopy P a)).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))) := by
  let inc := mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)
  have J := (boundedFlatCoefficientFullOpenChartFirstPasting f a
    ((underToLaurent R).app a) (polynomialUnderCoefficient_toLaurent R a)).postcomp inc
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    exact (congrArg (fun H => H.level n) (Homotopy.postcomp_trans
      (boundedFlatCoefficientFullOpenChartFirstTrack f a ((underToLaurent R).app a)
        (polynomialUnderCoefficient_toLaurent R a))
      (boundedFlatCoefficientFullOpenChartSecondTrack f a ((underToLaurent R).app a)) inc)).symm
  · intro n
    exact (positiveOuterTrack_level f a n).symm

/-- The original raw null retains its actual positive split track and source-leg contraction. -/
theorem originalNewNull_level (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a).level n =
    (((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientLaurentPlusHomotopy P a)).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
          (newConeLegNull f a)).level n := by
  change (Homotopy.precomp _
    (((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans _)).level n = _
  rw [Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

end CoefficientSectionEvaluationSeedComparison

/-- The actual original positive nulls compare through the unchanged Laurent movement. -/
def boundedFlatCoefficientFullOpenBassEvaluationNullPasting (a : Under R) :
    (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a).RelHomotopy
      ((boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a).trans
        (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a)) := by
  let inc := mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)
  let A := (boundedFlatCoefficientFullOpenChartFirstTrack f a ((underToLaurent R).app a)
    (polynomialUnderCoefficient_toLaurent R a)).postcomp inc
  let B := (boundedFlatCoefficientFullOpenChartSecondTrack f a
    ((underToLaurent R).app a)).postcomp inc
  let D := CoefficientSectionEvaluationSeedComparison.oldConeLegNull f a
  let E := CoefficientSectionEvaluationSeedComparison.newConeLegNull f a
  let L := boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a
  let T := (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientLaurentPlusHomotopy P a)).postcomp inc
  have J : (A.trans D).RelHomotopy (L.trans (T.trans E)) :=
    ((Homotopy.RelHomotopy.refl A).hcomp
      (CoefficientSectionEvaluationSeedComparison.positiveConePasting f a)).trans
      ((Homotopy.RelHomotopy.transAssoc A B E).symm.trans
        (((CoefficientSectionEvaluationSeedComparison.positiveChartPasting f a).hcomp
          (Homotopy.RelHomotopy.refl E)).trans
          (Homotopy.RelHomotopy.transAssoc L T E)))
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    exact CoefficientSectionEvaluationSeedComparison.originalOldNull_level f a n
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact CoefficientSectionEvaluationSeedComparison.originalNewNull_level f a n

/-- Original unit intertwining and original null pasting compare the actual based conjugates. -/
def boundedFlatCoefficientFullOpenBassEvaluationConjugation (a : Under R) :
    ((boundedFlatCoefficientFullOpenBassEvaluationOldUnit f a).conjugateToZero
      (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a)).RelHomotopy
    ((boundedFlatCoefficientFullOpenBassEvaluationNewUnit (P := P) a).conjugateToZero
      (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a)) :=
  Homotopy.RelHomotopy.conjugateNaturality
    (boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a)
    (boundedFlatCoefficientFullOpenBassEvaluationOldUnit f a)
    (boundedFlatCoefficientFullOpenBassEvaluationNewUnit (P := P) a)
    (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a)
    (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a)
    (boundedFlatCoefficientFullOpenBassEvaluationUnitPasting f a)
    (boundedFlatCoefficientFullOpenBassEvaluationNullPasting f a)

namespace CoefficientSectionEvaluationSeedComparison

/-- The initial conjugate is precisely the original fine seed followed by looped cone evaluation. -/
theorem originalFineSeed (a : Under R) :
    (boundedFlatCoefficientFullOpenBassEvaluationOldUnit f a).nullLoopMap
        (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a) =
      boundedFlatCoefficientFullOpenBassSeedMap f a ≫
        parameterLoopingMap (boundedFlatCoefficientFullOpenBassConeEvaluation f a) := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a))
    (boundedFlatCoefficientFullOpenBassConeEvaluation f a)
    ((boundedFlatCoefficientFullOpenLaurentHomotopy f a).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))))
    (boundedFlatCoefficientFullOpenBassEvaluationOldUnit f a)
    (boundedFlatCoefficientFullOpenBassNullHomotopy f a)
    (boundedFlatCoefficientFullOpenBassEvaluationOldNull f a)
    (by intro n; rfl) (by intro n; rfl)
  exact h.symm

/-- The final conjugate is precisely evaluation followed by the original raw positive seed. -/
theorem originalRawSeed (a : Under R) :
    (boundedFlatCoefficientFullOpenBassEvaluationNewUnit (P := P) a).nullLoopMap
        (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a) =
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
        boundedFlatCoefficientBassTransition P a := by
  have h := Homotopy.nullLoopMap_naturality
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))
    (boundedFlatCoefficientFullOpenBassEvaluationNewUnit (P := P) a)
    ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))
    (boundedFlatCoefficientFullOpenBassEvaluationNewNull (P := P) a)
    (boundedFlatCoefficientBassLaurentNullHomotopy P a)
    (by intro n; rfl) (by intro n; rfl)
  exact h

end CoefficientSectionEvaluationSeedComparison

/-- The whole pointed comparison of the original fine and raw one-step Bass seeds. -/
def boundedFlatCoefficientFullOpenBassSeedEvaluationHomotopy (a : Under R) :
    Homotopy (boundedFlatCoefficientFullOpenBassSeedMap f a ≫
      parameterLoopingMap (boundedFlatCoefficientFullOpenBassConeEvaluation f a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
        boundedFlatCoefficientBassTransition P a) :=
  (boundedFlatCoefficientFullOpenBassEvaluationConjugation f a).zeroLoopMapHomotopy.cast
    (CoefficientSectionEvaluationSeedComparison.originalFineSeed f a)
    (CoefficientSectionEvaluationSeedComparison.originalRawSeed (P := P) a)

/-- Comparison time and output-loop time remain independent at every original source point. -/
theorem boundedFlatCoefficientFullOpenBassSeedEvaluationHomotopy_apply
    (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientFullOpenBassSeedEvaluationHomotopy f a).level n (r, x)) s =
        (boundedFlatCoefficientFullOpenBassEvaluationConjugation f a).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
