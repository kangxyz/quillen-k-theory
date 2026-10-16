/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrismSides

/-! Named semantic consumers of the actual whole original reference families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
open Quillen.PerfectComplexes.BassMWholeNerve BassReferenceMerge BassH0Merge BassH1Join
namespace QuillenTest.MWholeNerveProductPrismSides
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)


/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_plus_s0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P c) false ![z.1, 0,
      z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1, z.2), StdSimplex.single
          2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_plus_s0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_plus_s1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P c) false ![z.1, 1,
      z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1, z.2), StdSimplex.single
          4)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_plus_s1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_plus_t0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P c) false ![z.1, z.2,
      0], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 z.1),
          NativeSquareFiveSimplex.parameter z.2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_plus_t0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_plus_t1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P c) false ![z.1, z.2,
      1], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 z.1),
          NativeSquareFiveSimplex.parameter z.2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_plus_t1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_minus_s0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert
      R) (laurentMinus_projection P c) true
      ![z.1, 0, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w
      (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1, unitInterval.symm z.2),
          StdSimplex.single 2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_minus_s0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_minus_s1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert
      R) (laurentMinus_projection P c) true
      ![z.1, 1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w
      (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1, unitInterval.symm z.2),
          StdSimplex.single 4)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_minus_s1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_minus_t0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert
      R) (laurentMinus_projection P c) true
      ![z.1, z.2, 0], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w
      (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 z.1),
          NativeSquareFiveSimplex.parameter z.2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_minus_t0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_product_minus_t1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert
      R) (laurentMinus_projection P c) true
      ![z.1, z.2, 1], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w
      (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 z.1),
          NativeSquareFiveSimplex.parameter z.2)), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.polynomial_product_minus_t1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_plus_s0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P d) false ![z.1, 0, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (z.2), StdSimplex.map
          CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 z.1))), by fun_prop⟩
            := by
  ext z
  exact BassMWholeNerve.chart_product_plus_s0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_plus_s1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P d) false ![z.1, 1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (z.2), StdSimplex.map
          CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 z.1))), by fun_prop⟩
            := by
  ext z
  exact BassMWholeNerve.chart_product_plus_s1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_plus_t0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P d) false ![z.1, z.2, 0], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 2, DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1,
          z.2))), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_product_plus_t0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_plus_t1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P d) false ![z.1, z.2, 1], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 4, DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1,
          z.2))), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_product_plus_t1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_minus_s0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d) true ![z.1, 0,
      z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (unitInterval.symm z.2), StdSimplex.map
          CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 z.1))), by fun_prop⟩
            := by
  ext z
  exact BassMWholeNerve.chart_product_minus_s0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_minus_s1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d) true ![z.1, 1,
      z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (unitInterval.symm z.2), StdSimplex.map
          CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 z.1))), by fun_prop⟩
            := by
  ext z
  exact BassMWholeNerve.chart_product_minus_s1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_minus_t0_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d) true ![z.1, z.2,
      0], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 4, DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1,
          z.2))), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_product_minus_t0_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_product_minus_t1_raw :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d) true ![z.1, z.2,
      1], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 2, DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1,
          z.2))), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_product_minus_t1_raw P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_plus_composition_side :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P c) false ![z.1, z.2,
      1], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 z.1, NativeSquareFiveSimplex.parameter z.2))), by fun_prop⟩
              := by
  ext z
  exact BassMWholeNerve.polynomial_plus_composition_side P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_polynomial_minus_composition_side :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert
      R) (laurentMinus_projection P c) true
      ![z.1, z.2, 0], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 z.1, NativeSquareFiveSimplex.parameter z.2))), by fun_prop⟩
              := by
  ext z
  exact BassMWholeNerve.polynomial_minus_composition_side P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_plus_composition_side :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
      (laurentPlus_projection P d) false ![z.1, 0, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter (z.2), binaryPath (k := 2) 0 1 2 z.1))), by
              fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_plus_composition_side P u v w z.1 z.2

/-- Equality of the entire compact original side maps, including every independent time. -/
theorem whole_chart_minus_composition_side :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d) true ![z.1, 0,
      z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
    ⟨fun z ↦ CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter (unitInterval.symm z.2), binaryPath (k := 2) 0 1 2
              z.1))), by fun_prop⟩ := by
  ext z
  exact BassMWholeNerve.chart_minus_composition_side P u v w z.1 z.2

/-- The complete fifteen-node family, including both actual canonical references. -/
theorem all_polynomial_plus_composition_side_nodes :
    (fun k : Fin 15 ↦ polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c)
      (polynomialSideIndex 0 k)) =
      (fun k ↦ coefficientPrismNodes P u v w
      (coefficientChartSideIndex BassH0Diagram.plusFace k)) := by
  funext k
  exact BassMWholeNerve.polynomial_plus_composition_side_nodes P u v w k

/-- The complete fifteen-node family, including both actual canonical references. -/
theorem all_polynomial_minus_composition_side_nodes :
    (fun k : Fin 15 ↦ polynomialProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P c)
      (polynomialSideIndex 0 k)) =
      (fun k ↦ coefficientPrismNodes P u v w
      (coefficientChartSideIndex BassH0Diagram.minusFace k)) := by
  funext k
  exact BassMWholeNerve.polynomial_minus_composition_side_nodes P u v w k

/-- The complete fifteen-node family, including both actual canonical references. -/
theorem all_chart_plus_composition_side_nodes :
    (fun k : Fin 15 ↦ chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d)
      (chartSideIndex 1 k)) =
      (fun k ↦ laurentPrismNodes P u v w
      (laurentPolynomialSideIndex BassH0Diagram.plusFace k)) := by
  funext k
  exact BassMWholeNerve.chart_plus_composition_side_nodes P u v w k

/-- The complete fifteen-node family, including both actual canonical references. -/
theorem all_chart_minus_composition_side_nodes :
    (fun k : Fin 15 ↦ chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection
      P d)
      (chartSideIndex 1 k)) =
      (fun k ↦ laurentPrismNodes P u v w
      (laurentPolynomialSideIndex BassH0Diagram.minusFace k)) := by
  funext k
  exact BassMWholeNerve.chart_minus_composition_side_nodes P u v w k

/-- Every native level retains the original point and independent structure coordinate. -/
theorem original_polynomial_product_side_point
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
      (polynomialProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n := by
  apply BassMWholeNerve.polynomial_product_side_point

/-- Every native level retains the original point and independent structure coordinate. -/
theorem original_polynomial_product_side_structure
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) (n + 1)
      (polynomialProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap n x
          t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
          (polynomialProductParameter.{u} inverse z, x)) t := by
  apply BassMWholeNerve.polynomial_product_side_structure

/-- Every native level retains the original point and independent structure coordinate. -/
theorem original_chart_product_side_point
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
      (chartProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n := by
  apply BassMWholeNerve.chart_product_side_point

/-- Every native level retains the original point and independent structure coordinate. -/
theorem original_chart_product_side_structure
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) (n + 1)
      (chartProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap n x
          t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
          (chartProductParameter.{u} inverse z, x)) t := by
  apply BassMWholeNerve.chart_product_side_structure

end QuillenTest.MWholeNerveProductPrismSides
