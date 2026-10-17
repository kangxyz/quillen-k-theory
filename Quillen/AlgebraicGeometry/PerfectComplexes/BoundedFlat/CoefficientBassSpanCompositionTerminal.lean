/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionTree
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrismEndpoints

/-!
# The two original terminal polynomial paths

The terminal row keeps both original geometric square paths at their literal half speeds.
Their full five-node references are the original postcomposition and precomposition families.
The common node is retained, and the last endpoint is the exact coefficient-path attachment.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassH0Merge BassH1Join DoubleSquareScalarPaths
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "F" => polynomialReference P p q

/-- A complete original vertex, in the fixed polynomial-source reference. -/
def polynomialVertex (i : Fin 18) : |parameterSSet F| :=
  CommonReferenceNerve.parameter F (squareNodes P p q) (StdSimplex.single i)

/-- All five first-square nodes keep their original postcomposition and reanchoring. -/
def terminalFirstNodes (i : Fin 5) : CommonReferenceNerve.Node F :=
  anchorNode (squareAnchor P p q)
    (postReferenceNode (originalReference P p q)
      (BassMWholeNerve.coefficientModel P ((polynomialUnderFunctor R).map q))
      (H := CoefficientSquareFamilies.polynomialSource P p)
      (BassMWholeNerve.polynomialFirstAnchor P p q)
      (CoefficientSquareFamilies.polynomialNodes P p i))

/-- All five second-square nodes keep their original precomposition and reanchoring. -/
def terminalSecondNodes (i : Fin 5) : CommonReferenceNerve.Node F :=
  anchorNode (squareAnchor P p q)
    (preReferenceNode (originalReference P p q) (BassMWholeNerve.coefficientModel P p)
      (H := CoefficientSquareFamilies.polynomialSource P q)
      (BassMWholeNerve.polynomialSecondAnchor P p q)
      (CoefficientSquareFamilies.polynomialNodes P q i))

/-- The full first row is the postcomposed first original polynomial square. -/
theorem terminal_first_nodes (i : Fin 5) :
    squareNodes P p q (CoefficientMovingSquareRows.firstRow i) = terminalFirstNodes P p q i :=
  congrArg (anchorNode (squareAnchor P p q)) (BassMWholeNerve.polynomial_first_nodes P p q i)

/-- The full second row is the precomposed second original polynomial square. -/
theorem terminal_second_nodes (i : Fin 5) :
    squareNodes P p q (CoefficientMovingSquareRows.secondRow i) = terminalSecondNodes P p q i :=
  congrArg (anchorNode (squareAnchor P p q)) (BassMWholeNerve.polynomial_second_nodes P p q i)

/-- The first complete original path starts at node seventeen and ends at the shared node. -/
def terminalFirstPath : Path (polynomialVertex P p q 17) (polynomialVertex P p q 13) :=
  (lastRestriction.symm.trans middleChart).map
    (CommonReferenceNerve.parameter F (squareNodes P p q)).continuous

/-- The second complete original path starts at the same node and ends at node eleven. -/
def terminalSecondPath : Path (polynomialVertex P p q 13) (polynomialVertex P p q 11) :=
  (secondRestriction.symm.trans firstRestriction).map
    (CommonReferenceNerve.parameter F (squareNodes P p q)).continuous

/-- The terminal scalar word is the two unchanged original square words. -/
theorem terminal_scalar : originalComparisonSource =
    (lastRestriction.symm.trans middleChart).trans
      (secondRestriction.symm.trans firstRestriction) := by
  simp only [originalComparisonSource, Path.trans_symm, Path.symm_symm]

/-- The first full terminal half has its original speed, including both endpoints. -/
theorem polynomialSquare_terminal_lower (s : I) :
    polynomialSquare P p q (1, lower s) = terminalFirstPath P p q s := by
  change CommonReferenceNerve.parameter F (squareNodes P p q)
    (coefficientMovingSquareParameter (1, lower s)) = _
  rw [CoefficientMovingSquareRows.moving_one, terminal_scalar, path_lower]; rfl

/-- The second full terminal half has its independent original speed. -/
theorem polynomialSquare_terminal_upper (s : I) :
    polynomialSquare P p q (1, upper s) = terminalSecondPath P p q s := by
  change CommonReferenceNerve.parameter F (squareNodes P p q)
    (coefficientMovingSquareParameter (1, upper s)) = _
  rw [CoefficientMovingSquareRows.moving_one, terminal_scalar, path_upper]; rfl

/-- The entire terminal row is the literal half-speed concatenation of these two paths. -/
theorem polynomialSquare_terminal (s : I) :
    polynomialSquare P p q (1, s) =
      ((terminalFirstPath P p q).trans (terminalSecondPath P p q)) s := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [polynomialSquare_terminal_lower, path_lower]
  · rw [polynomialSquare_terminal_upper, path_upper]

/-- The first path uses only the four ordered supports of its full five-node family. -/
theorem terminalFirstPath_parameter (s : I) :
    terminalFirstPath P p q s =
      CommonReferenceNerve.parameter F (terminalFirstNodes P p q)
        (NativeSquareFiveSimplex.parameter s) := by
  change CommonReferenceNerve.parameter F (squareNodes P p q)
    ((lastRestriction.symm.trans middleChart) s) = _
  have hs := BassSupportOrder.map_two_binary CoefficientMovingSquareRows.firstRow 0 1 2 3 4 s
  change StdSimplex.map CoefficientMovingSquareRows.firstRow
    (NativeSquareFiveSimplex.parameter s) = (lastRestriction.symm.trans middleChart) s at hs
  rw [← hs]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  change StdSimplex.map (BassH1Support.edgeFace i).toOrderHom z =
    NativeSquareFiveSimplex.parameter s at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F (terminalFirstNodes P p q) (squareNodes P p q)
    CoefficientMovingSquareRows.firstRow (terminal_first_nodes P p q)
    (BassH1Support.edgeFace i) (CoefficientMovingSquareRows.primitive_rows_monotone 1 i) z

/-- The second path likewise uses its four actual supports, without a global monotonicity claim. -/
theorem terminalSecondPath_parameter (s : I) :
    terminalSecondPath P p q s =
      CommonReferenceNerve.parameter F (terminalSecondNodes P p q)
        (NativeSquareFiveSimplex.parameter s) := by
  change CommonReferenceNerve.parameter F (squareNodes P p q)
    ((secondRestriction.symm.trans firstRestriction) s) = _
  have hs := BassSupportOrder.map_two_binary CoefficientMovingSquareRows.secondRow 0 1 2 3 4 s
  change StdSimplex.map CoefficientMovingSquareRows.secondRow
    (NativeSquareFiveSimplex.parameter s) = (secondRestriction.symm.trans firstRestriction) s at hs
  rw [← hs]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  change StdSimplex.map (BassH1Support.edgeFace i).toOrderHom z =
    NativeSquareFiveSimplex.parameter s at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F (terminalSecondNodes P p q) (squareNodes P p q)
    CoefficientMovingSquareRows.secondRow (terminal_second_nodes P p q)
    (BassH1Support.edgeFace i) (CoefficientMovingSquareRows.primitive_rows_monotone 2 i) z

/-- The two original terminal families meet at the same complete dependent node. -/
theorem terminal_join_node : terminalFirstNodes P p q 4 = terminalSecondNodes P p q 2 :=
  (terminal_first_nodes P p q 4).symm.trans (terminal_second_nodes P p q 2)

/-- The last complete node is literally the polynomial attachment of the coefficient endpoint. -/
theorem terminal_last_node : squareNodes P p q 11 =
    postcompNode (polynomialMap P (c := c)) (coefficientNodes P p q 2) :=
  square_source_nodes P p q 2

/-- The last path endpoint is the whole coefficient-path attachment, with its original reference. -/
theorem terminalSecondPath_attachment : terminalSecondPath P p q 1 =
    mapParameter (postcompNode (polynomialMap P (c := c))) (coefficientPath P p q 1) := by
  rw [← polynomialSquare_terminal_upper]
  have h : upper 1 = 1 := Subtype.ext (by norm_num [upper])
  rw [h, polynomialSquare_right]

/-- The first path starts at the actual target-composition endpoint. -/
theorem terminalFirstPath_targetAttachment : terminalFirstPath P p q 0 =
    mapParameter (targetAttachmentNode P p q)
      (coefficientPath P ((polynomialUnderFunctor R).map p)
        ((polynomialUnderFunctor R).map q) 1) := by
  rw [← polynomialSquare_terminal_lower]
  have h : lower 0 = 0 := Subtype.ext (by norm_num [lower])
  rw [h, polynomialSquare_left]

/-- Every first-half value is the postcomposed original first square, in every degree. -/
theorem terminalFirstPath_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily F n (terminalFirstPath P p q s) x =
      ((boundedFlatCoefficientPolynomialSquareHomotopy P p).postcomp
        (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map q)))).level n (s, x) := by
  rw [← polynomialSquare_terminal_lower, polynomialSquare_original_native,
    (boundedFlatCoefficientPolynomialCompositionSquare P p q).at_one]
  exact Quillen.LoopPrespectrum.Homotopy.trans_lower_cell _ _ n s x

/-- Every second-half value is the precomposed original second square, with its native cast. -/
theorem terminalSecondPath_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily F n (terminalSecondPath P p q s) x =
      (Quillen.LoopPrespectrum.Homotopy.precomp
        (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
        (boundedFlatCoefficientPolynomialSquareHomotopy P q)).level n (s, x) := by
  rw [← polynomialSquare_terminal_upper, polynomialSquare_original_native,
    (boundedFlatCoefficientPolynomialCompositionSquare P p q).at_one]
  exact Quillen.LoopPrespectrum.Homotopy.trans_upper_cell _ _ n s x

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
