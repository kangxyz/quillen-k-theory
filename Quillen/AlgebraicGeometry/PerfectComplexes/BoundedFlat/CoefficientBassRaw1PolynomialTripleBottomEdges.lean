/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleBottom

/-!
# The four original half-boundaries of the polynomial triple bottom

The original split-triple comparison surface meets both radial caps, the actual
positive and negative postcomposition caps, and the placed input cap. All equalities
hold in the first polynomial sheet, with the complete source references and original
binary clocks retained before native evaluation.
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBottomEdges
open CommonReferenceNerve BassH0Merge
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces
open CoefficientBassRaw1PolynomialTripleBottom
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

private theorem simplex_binary (i j k : Fin 8) (hij : i ≤ j) (hjk : j ≤ k) (r : I) :
    simplex P β p q w (binaryPath i j k r) =
    CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w
      (parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d))
        (fun t ↦ CoefficientBassRaw1PolynomialTripleBottom.nodes P β p q w (![i, j, k] t))
        (binaryPath (k := 2) 0 1 2 r)) := by
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w)
  have h := parameter_face (polynomialReference P p q w ≫ normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialTripleBottom.nodes P β p q w)
    (SplitTripleSimplex.triangleFace i j k hij hjk) (binaryPath (k := 2) 0 1 2 r)
  rw [BassSupportOrder.map_any_binary] at h
  exact h

/-- The first half of the original left boundary is the actual left radial lower face. -/
theorem family_zero_lower (r : I) :
    family P β p q w (0, lower r) =
      CoefficientBassRaw1PolynomialRadialCaps.left P β p q w (r, 0) := by
  rw [family_zero, SplitTripleSimplex.splitLeftPath, path_lower]
  refine (simplex_binary P β p q w 0 1 2 (by decide) (by decide) r).trans ?_
  exact (CoefficientBassRaw1PolynomialRadialCaps.left_lower P β p q w r).symm

/-- The first half of the original right boundary is the actual right radial lower face. -/
theorem family_one_lower (r : I) :
    family P β p q w (1, lower r) =
      CoefficientBassRaw1PolynomialRadialCaps.right P β p q w (r, 0) := by
  rw [family_one, SplitTripleSimplex.splitRightPath, path_lower]
  refine (simplex_binary P β p q w 0 4 5 (by decide) (by decide) r).trans ?_
  exact (CoefficientBassRaw1PolynomialRadialCaps.right_lower P β p q w r).symm

private theorem family_zero_upper_parameter (r : I) :
    family P β p q w (0, upper r) =
    CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w
      (mapParameter (postcompNodeLower P β p q w)
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  rw [family_zero, SplitTripleSimplex.splitLeftPath, path_upper]
  refine (simplex_binary P β p q w 2 3 7 (by decide) (by decide) r).trans ?_
  dsimp only [CoefficientBassLaurentCompositionCarrier.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter]
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w)
  apply congrArg (fun N ↦ parameter _ N (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact (postcomp_node_row P β p q w i).symm

/-- The second left half is the lower face of the actual positive postcomposition cap. -/
theorem family_zero_upper_plus (r : I) :
    family P (underToLaurent R) p q w (0, upper r) =
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (r, 0)) := by
  rw [family_zero_upper_parameter]
  have h := postcomp_lower_parameter P (underToLaurent R) p q w
    (CoefficientBassLaurentCompositionCarrier.family P p q r)
  exact ((plus_postcomp_lower_family P p q w r).trans (congrArg _ h.symm)).symm

/-- The second left half is the lower face of the actual negative postcomposition cap. -/
theorem family_zero_upper_minus (r : I) :
    family P (underToLaurentInvert R) p q w (0, upper r) =
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (r, 0)) := by
  rw [family_zero_upper_parameter]
  have h := postcomp_lower_parameter P (underToLaurentInvert R) p q w
    (CoefficientBassLaurentCompositionCarrier.family P p q r)
  exact ((minus_postcomp_lower_family P p q w r).trans (congrArg _ h.symm)).symm

/-- The second right half is the actual placed input cap's entire lower face. -/
theorem family_one_upper (r : I) :
    family P β p q w (1, upper r) =
      CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (r, 0) := by
  rw [family_one, SplitTripleSimplex.splitRightPath, path_upper]
  refine (simplex_binary P β p q w 5 6 7 (by decide) (by decide) r).trans ?_
  have h := input_lower_parameter P β p q w
    (CoefficientBassLaurentCompositionCarrier.family P q w r)
  have hh := (input_placed_lower_family P β p q w r).trans (congrArg _ h.symm)
  refine Eq.trans ?_ hh.symm
  dsimp only [CoefficientBassLaurentCompositionCarrier.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter]
  apply congrArg (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w)
  apply congrArg (fun N ↦ parameter _ N (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact (input_node_row P β p q w i).symm

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBottomEdges
