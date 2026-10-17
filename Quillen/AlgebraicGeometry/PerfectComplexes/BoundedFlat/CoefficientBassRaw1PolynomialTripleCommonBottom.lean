/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleFillerFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonRadialCaps

/-! Full eight-node triple bottoms retain their exact Laurent18 placement in the common sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleCommonBottom
open CommonReferenceNerve
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces
open CoefficientBassRaw1PolynomialCommonRadialCaps CoefficientBassRaw1PolynomialTripleRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- Every point of the full first eight-node simplex has its original Laurent18 placement. -/
theorem first_simplex (x : StdSimplex ℝ (Fin 8)) :
    CoefficientBassRaw1PolynomialTripleBottom.simplex P β
      ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f) x =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
      (parameter (targetReference P α β f) (nodes P α β f)
        (StdSimplex.map DoubleSquareMergedSimplex.firstFace.toOrderHom x)) := by
  change CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
    (parameter (targetReference P α β f)
      (CoefficientBassRaw1PolynomialTripleBottom.nodes P β
        ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f)) x) = _
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
  rw [parameter_face]
  exact congrArg (fun N ↦ parameter (targetReference P α β f) N x)
    (funext (first_triple_nodes P α β f))

/-- The whole middle simplex keeps its full original chart-square reference transport. -/
theorem middle_simplex (x : StdSimplex ℝ (Fin 8)) :
    CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f
      (CoefficientBassRaw1PolynomialTripleBottom.simplex P β
        ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
          (α.app b) x) =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
      (parameter (targetReference P α β f) (nodes P α β f)
        (StdSimplex.map DoubleSquareMergedSimplex.middleFace.toOrderHom x)) := by
  dsimp only [CoefficientBassRaw1PolynomialTripleBottom.simplex, ContinuousMap.comp_apply]
  rw [CoefficientBassRaw1PolynomialCapLowerFaces.middleMap_laurent]
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
  refine (mapParameter_parameter (CommonReferenceProduct.reanchor (middleTransport P α β f))
    (CoefficientBassRaw1PolynomialTripleBottom.nodes P β
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
        (α.app b)) x).trans ?_
  exact (congrArg (fun N ↦ parameter (targetReference P α β f) N x)
    (funext (middle_triple_nodes P α β f))).trans
      (parameter_face (targetReference P α β f) (nodes P α β f)
        DoubleSquareMergedSimplex.middleFace x).symm

/-- The whole last simplex keeps both original square transports and association. -/
theorem last_simplex (x : StdSimplex ℝ (Fin 8)) :
    CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f
      (CoefficientBassRaw1PolynomialTripleBottom.simplex P β f
        ((polynomialUnderCoefficient R).app b) (α.app b) x) =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
      (parameter (targetReference P α β f) (nodes P α β f)
        (StdSimplex.map DoubleSquareMergedSimplex.lastFace.toOrderHom x)) := by
  dsimp only [CoefficientBassRaw1PolynomialTripleBottom.simplex, ContinuousMap.comp_apply]
  rw [CoefficientBassRaw1PolynomialCapLowerFaces.lastMap_laurent]
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f)
  refine (mapParameter_parameter (CommonReferenceProduct.reanchor (lastTransport P α β f))
    (CoefficientBassRaw1PolynomialTripleBottom.nodes P β
      f ((polynomialUnderCoefficient R).app b) (α.app b)) x).trans ?_
  exact (congrArg (fun N ↦ parameter (targetReference P α β f) N x)
    (funext (last_triple_nodes P α β f))).trans
      (parameter_face (targetReference P α β f) (nodes P α β f)
        DoubleSquareMergedSimplex.lastFace x).symm

variable (negative : Bool)

/-- The actual first filler bottom retains its complete original split-triple surface. -/
theorem first_extension_bottom (s r : I) :
    CoefficientBassRaw1PolynomialTripleFiller.extension P
      ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f)
        negative ![s, r, 0] =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α (chartChoice negative) f
      (parameter (targetReference P α (chartChoice negative) f)
        (nodes P α (chartChoice negative) f)
        (StdSimplex.map DoubleSquareMergedSimplex.firstFace.toOrderHom
          (SplitTripleSimplex.comparisonParameter (s, r)))) := by
  rw [CoefficientBassRaw1PolynomialTripleFiller.extension_bottom]
  exact first_simplex P α (chartChoice negative) f _

/-- The actual middle filler bottom retains both clocks after its original normalization. -/
theorem middle_extension_bottom (s r : I) :
    CoefficientBassRaw1PolynomialCommonSheet.middleMap P α (chartChoice negative) f
      (CoefficientBassRaw1PolynomialTripleFiller.extension P
        ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f)
          (α.app b) negative ![s, r, 0]) =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α (chartChoice negative) f
      (parameter (targetReference P α (chartChoice negative) f)
        (nodes P α (chartChoice negative) f)
        (StdSimplex.map DoubleSquareMergedSimplex.middleFace.toOrderHom
          (SplitTripleSimplex.comparisonParameter (s, r)))) := by
  rw [CoefficientBassRaw1PolynomialTripleFiller.extension_bottom]
  exact middle_simplex P α (chartChoice negative) f _

/-- The actual last filler bottom retains both clocks after its original normalization. -/
theorem last_extension_bottom (s r : I) :
    CoefficientBassRaw1PolynomialCommonSheet.lastMap P α (chartChoice negative) f
      (CoefficientBassRaw1PolynomialTripleFiller.extension P f
        ((polynomialUnderCoefficient R).app b) (α.app b) negative ![s, r, 0]) =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α (chartChoice negative) f
      (parameter (targetReference P α (chartChoice negative) f)
        (nodes P α (chartChoice negative) f)
        (StdSimplex.map DoubleSquareMergedSimplex.lastFace.toOrderHom
          (SplitTripleSimplex.comparisonParameter (s, r)))) := by
  rw [CoefficientBassRaw1PolynomialTripleFiller.extension_bottom]
  exact last_simplex P α (chartChoice negative) f _

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleCommonBottom
