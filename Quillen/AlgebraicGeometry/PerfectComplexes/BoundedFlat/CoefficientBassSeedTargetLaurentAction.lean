/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCutOpenAugmentationEvaluation

/-! The full Laurent action and the prescribed target action on original polynomial sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetLaurentAction
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))

/-- The normalized original Laurent coefficient action of the arrow `f`. -/
abbrev laurentAction := BassH0Merge.normalizedMap
  (coefficientMap P ((laurentUnderFunctor R).map f))

/-- The complete dependent node is postcomposed, including its reference isomorphism. -/
def nodeMap : Node G → Node (G ≫ laurentAction P f) :=
  postcompNode (laurentAction P f)

/-- The action is defined on the whole nerve, not only on native vertices. -/
def parameterMap := mapParameter (nodeMap P f G)

theorem parameterMap_parameter {k : ℕ} (N : Fin (k + 1) → Node G)
    (z : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    parameterMap P f G (parameter G N z) =
      parameter (G ≫ laurentAction P f) (fun i ↦ nodeMap P f G (N i)) z :=
  mapParameter_parameter _ _ _

/-- The whole Laurent family has the original coefficient action at every level. -/
theorem parameterMap_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (G ≫ laurentAction P f) n (parameterMap P f G y) x =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map f))).map n
          (pointwisePrespectrumFamily G n y x) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  rw [parameterMap_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact prespectrumFamily_postcomp N (laurentAction P f) n z x

/-- The actual cone map agrees with the full Laurent action on its entire base summand. -/
theorem inclusion_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum V).space n) :
    (boundedFlatCoefficientBassConeMap P f).map n
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n
        (pointwisePrespectrumFamily G n y x)) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
      (pointwisePrespectrumFamily (G ≫ laurentAction P f) n (parameterMap P f G y) x) := by
  rw [parameterMap_native]
  exact congrArg (fun h ↦ h.map n (pointwisePrespectrumFamily G n y x))
    (boundedFlatCoefficientBassConeMap_inclusion P f)

variable (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
  (space (op P, (polynomialUnderFunctor R).obj a))))

/-- A polynomial sheet is sent through the original moving chart square and contraction. -/
theorem sheet_native (n : ℕ) (y : |parameterSSet D|) (t : I)
    (x : (prespectrum V).space n) :
    (boundedFlatCoefficientBassConeMap P f).map n
      (BassProjectionPath.WholeReference.FourEdge.originalSheetValue P a D n
        (y, ULift.up t) x) =
    (((boundedFlatCoefficientBassComparisonHomotopy P f).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))).trans
      (Homotopy.precomp (boundedFlatCoefficientPolynomialSpanMap P f)
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b)))).level n
      (t, HomotopyPushout.left
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
        (pointwisePrespectrumFamily D n y x)) :=
  boundedFlatCoefficientBassConeMap_cylinder P f n t _

end Quillen.PerfectComplexes.CoefficientBassSeedTargetLaurentAction
