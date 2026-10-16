/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrismEndpoints
import QuillenTest.CommonReferenceProductNodes

/-! Whole compact face maps, full references and original native terminal-cube consumers. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes Quillen.PerfectComplexes.BassMWholeNerve
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveProductPrismEndpoints
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_polynomial_product_plus_source_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P c) false ![0, z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w)) (h0Anchor P (u ≫ v) w)
        ![1, upper z.1, lower z.2], by fun_prop⟩ := by
  ext z
  exact polynomial_product_plus_source_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_chart_product_plus_source_face :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P d) false ![0, z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w)
        ![1, upper z.1, lower z.2], by fun_prop⟩ := by
  ext z
  exact chart_product_plus_source_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_polynomial_product_plus_target_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P c) false ![1, z.1, upper z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ precompLift P u v w ![1, upper z.1, lower z.2], by fun_prop⟩ := by
  ext z
  exact polynomial_product_plus_target_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_chart_product_plus_target_face :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P d) false ![1, lower z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ postcompLift P u v w ![1, upper z.1, lower z.2], by fun_prop⟩ := by
  ext z
  exact chart_product_plus_target_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_product_plus_middle_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P c) false ![1, z.1, lower z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ chartProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P d) false ![1, upper z.1, z.2], by fun_prop⟩ := by
  ext z
  exact product_plus_middle_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_polynomial_product_minus_source_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P c) true ![0, z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w)) (h0Anchor P (u ≫ v) w)
        ![1, upper z.1, upper (upper z.2)], by fun_prop⟩ := by
  ext z
  exact polynomial_product_minus_source_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_chart_product_minus_source_face :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P d) true ![0, z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w)
        ![1, upper z.1, upper (upper z.2)], by fun_prop⟩ := by
  ext z
  exact chart_product_minus_source_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_polynomial_product_minus_target_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P c) true ![1, z.1, lower z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ precompLift P u v w ![1, upper z.1, upper (upper z.2)], by fun_prop⟩ := by
  ext z
  exact polynomial_product_minus_target_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_chart_product_minus_target_face :
    (⟨fun z : unitInterval × unitInterval ↦ chartProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P d) true ![1, lower z.1, z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ postcompLift P u v w ![1, upper z.1, upper (upper z.2)], by fun_prop⟩ := by
  ext z
  exact chart_product_minus_target_face P u v w z.1 z.2

/-- The two compact whole face maps agree at every original pair of parameters. -/
theorem whole_product_minus_middle_face :
    (⟨fun z : unitInterval × unitInterval ↦ polynomialProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P c) true ![1, z.1, upper z.2], by fun_prop⟩ :
      C(unitInterval × unitInterval, |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|)) =
      ⟨fun z ↦ chartProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P d) true ![1, upper z.1, z.2], by fun_prop⟩ := by
  ext z
  exact product_minus_middle_face P u v w z.1 z.2

/-- Compact evaluation on the attached face is the entire unchanged original native cube. -/
theorem actual_polynomial_plus_target_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P c) false) n
      (![1, s, upper t], x) =
      (BassMWhole.interiorCube P v w).level n
        (1, (upper s, (lower t,
          (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _ (precompNodes P u v w)
    ![1, s, upper t] (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
    (polynomial_product_plus_target_face P u v w s t) n x).trans
      (precomp_native_cube P u v w n 1 (upper s) (lower t) x)

/-- Compact evaluation on the attached face is the entire unchanged original native cube. -/
theorem actual_polynomial_minus_target_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P c) true) n
      (![1, s, lower t], x) =
      (BassMWhole.interiorCube P v w).level n
        (1, (upper s, (upper (upper t),
          (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _ (precompNodes P u v w)
    ![1, s, lower t] (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
    (polynomial_product_minus_target_face P u v w s t) n x).trans
      (precomp_native_cube P u v w n 1 (upper s) (upper (upper t)) x)

/-- Compact evaluation on the attached face is the entire unchanged original native cube. -/
theorem actual_chart_plus_target_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurent R)
        (laurentPlus_projection P d) false) n
      (![1, lower s, t], x) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map w))).map n
        ((BassMWhole.interiorCube P u v).level n (1, (upper s, (lower t, x)))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _ (postcompNodes P u v w)
    ![1, lower s, t] (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
    (chart_product_plus_target_face P u v w s t) n x).trans
      (postcomp_native_cube P u v w n 1 (upper s) (lower t) x)

/-- Compact evaluation on the attached face is the entire unchanged original native cube. -/
theorem actual_chart_minus_target_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurentInvert R)
        (laurentMinus_projection P d) true) n
      (![1, lower s, t], x) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map w))).map n
        ((BassMWhole.interiorCube P u v).level n (1, (upper s, (upper (upper t), x)))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _ (postcompNodes P u v w)
    ![1, lower s, t] (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
    (chart_product_minus_target_face P u v w s t) n x).trans
      (postcomp_native_cube P u v w n 1 (upper s) (upper (upper t)) x)

/-- Every one of the twenty-five actual middle nodes keeps its complete reference. -/
theorem actual_plus_middle_full_node (i j : Fin 5) :
    polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c)
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.firstRow i, j)) =
      chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d)
        (Quillen.SimplexGrid.index 4 17 (i, CoefficientMovingSquareRows.secondRow j)) :=
  product_middle_nodes P u v w _ _ _ i j

/-- Every one of the twenty-five actual middle nodes keeps its complete reference. -/
theorem actual_minus_middle_full_node (i j : Fin 5) :
    polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.firstRow i, j)) =
      chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
        (Quillen.SimplexGrid.index 4 17 (i, CoefficientMovingSquareRows.secondRow j)) :=
  product_middle_nodes P u v w _ _ _ i j

end QuillenTest.MWholeNerveProductPrismEndpoints
