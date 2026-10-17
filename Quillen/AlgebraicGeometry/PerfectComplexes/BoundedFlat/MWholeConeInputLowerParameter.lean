/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLowerAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassReverseFiniteProduct

/-! The full lower parameter of both finite-source polynomial cells in the ordinary input cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct

private theorem lower_parameter {V W T U X : Model.{v}}
    (D : V ⟶ W) (F : W ⟶ T) (J : T ⟶ U) (C : W ⟶ X) (L : X ⟶ U)
    (G : V ⟶ U) (a : G.functor ≅ ((D ≫ F) ≫ J).functor)
    (l : (F ≫ J).functor ≅ (C ≫ L).functor) {k m : ℕ}
    (Z : Fin (k + 1) → Node D) (M : Fin (m + 1) → Node L)
    (z : StdSimplex ℝ (Fin (k + 1))) (w : StdSimplex ℝ (Fin (m + 1))) :
    mapParameter (reanchor a) (FiniteSourceSheet.laurent D F J Z
      (mapParameter (fun N ↦ reanchor l (precompNode C N))
        (CommonReferenceNerve.parameter L M w), z)) =
    FiniteParameter.parameter (D ≫ C) G
      (fun N j ↦ node G (D ≫ C) L
        (a ≪≫ Functor.associator D.functor F.functor J.functor ≪≫
          isoWhiskerLeft D.functor l ≪≫ (Functor.associator D.functor C.functor L.functor).symm)
        N (M j))
      (mapParameter (postcompNode C) (CommonReferenceNerve.parameter D Z z), w) := by
  change mapParameter _ (FiniteParameter.parameter (F ≫ J) ((D ≫ F) ≫ J) _
    (mapParameter _ (CommonReferenceNerve.parameter L M w), z)) = _
  rw [mapParameter_parameter, mapParameter_parameter]
  rw [← CoefficientBassReverseFiniteProduct.finite_product_parameter_exchange]
  rw [FiniteParameter.parameter_characteristic,
    mapParameter_parameter, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns
    (Quillen.SimplexGrid.parameter m k (w, z)))
  funext i
  exact lower_product_node D F J C L G a l
    (Z ((Quillen.SimplexGrid.indexEquiv m k).symm i).2)
    (M ((Quillen.SimplexGrid.indexEquiv m k).symm i).1)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "D" => sourceReference P p
local notation "F" => pairReference P q w
local notation "L" => CoefficientBassLaurentCompositionCarrier.reference P q w
local notation "S" => normalizedMap (coefficientMap P p) ≫ BassProjectionPath.source P b
local notation "G" => BassProjectionPath.WholeReference.reference P d (input P p q w)
variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (β.app b) ≫ polynomialProjection P b = laurentProjection P b)
local notation "C" => BassMWholeNerve.coefficientModel P (β.app b)

/-- The original polynomial square at the target has its explicit inverse node-four anchor. -/
def lowerSurface : C(I, |parameterSSet S|) :=
  (mapParameter (fun N ↦ reanchor (lowerSurfaceAnchor P p β hb) (postcompNode C N))).comp
    ((CommonReferenceNerve.parameter D (CoefficientSquareFamilies.polynomialNodes P p)).comp
      NativeSquareFiveSimplex.parameter)

/-- The common midpoint product retains the original binary Laurent clock. -/
def midpointProduct : C(|parameterSSet S| × I, |parameterSSet G|) :=
  (FiniteParameter.parameter S G
    (fun N j ↦ node G S L (midpointAnchor P p q w) N
      (CoefficientBassLaurentCompositionCarrier.nodes P q w j))).comp
    ⟨fun z ↦ (z.1, binaryPath (k := 2) 0 1 2 z.2), by fun_prop⟩

private theorem lower_parameter_midpoint
    (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (ha : lowerProductAnchor P p q w β hd = midpointAnchor P p q w ≪≫
      isoWhiskerRight (lowerSurfaceAnchor P p β hb) (L).functor) (r t : I) :
    laurentPlacement P p q w β hd
      (FiniteSourceSheet.laurent D F (BassMWholeNerve.coefficientModel P (β.app d))
        (CoefficientSquareFamilies.polynomialNodes P p)
        (mapParameter (fun N ↦ reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) (precompNode C N))
          (CoefficientBassLaurentCompositionCarrier.family P q w r),
          NativeSquareFiveSimplex.parameter t)) =
      midpointProduct P p q w (lowerSurface P p β hb t, r) := by
  change mapParameter _ (FiniteSourceSheet.laurent _ _ _ _
    (mapParameter _ (CommonReferenceNerve.parameter L
      (CoefficientBassLaurentCompositionCarrier.nodes P q w) (binaryPath (k := 2) 0 1 2 r)),
      NativeSquareFiveSimplex.parameter t)) = _
  rw [lower_parameter]
  change FiniteParameter.parameter (D ≫ C) G
    (fun N j ↦ node G (D ≫ C) L (lowerProductAnchor P p q w β hd) N
      (CoefficientBassLaurentCompositionCarrier.nodes P q w j))
    (mapParameter (postcompNode C) (CommonReferenceNerve.parameter D
      (CoefficientSquareFamilies.polynomialNodes P p) (NativeSquareFiveSimplex.parameter t)),
      binaryPath (k := 2) 0 1 2 r) = _
  rw [ha]
  change _ = FiniteParameter.parameter S G _
    (mapParameter (fun N ↦ reanchor (lowerSurfaceAnchor P p β hb) (postcompNode C N))
      (CommonReferenceNerve.parameter D (CoefficientSquareFamilies.polynomialNodes P p)
        (NativeSquareFiveSimplex.parameter t)), binaryPath (k := 2) 0 1 2 r)
  rw [mapParameter_parameter, mapParameter_parameter,
    FiniteParameter.parameter_characteristic, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter G ns
    (Quillen.SimplexGrid.parameter 4 2
      (NativeSquareFiveSimplex.parameter t, binaryPath (k := 2) 0 1 2 r)))
  funext i
  exact (node_first_reanchor G S (D ≫ C) L (lowerSurfaceAnchor P p β hb)
    (midpointAnchor P p q w)
    (postcompNode C (CoefficientSquareFamilies.polynomialNodes P p
      ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).1))
    (CoefficientBassLaurentCompositionCarrier.nodes P q w
      ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).2)).symm

/-- The positive cell meets the exact common midpoint Laurent product. -/
theorem plus_lower_parameter (r t : I) :
    laurentPlacement P p q w (underToLaurent R) (laurentPlus_projection P d)
      (FiniteSourceSheet.laurent D F
        (BassMWholeNerve.coefficientModel P ((underToLaurent R).app d))
        (CoefficientSquareFamilies.polynomialNodes P p)
        (mapParameter (fun N ↦ reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P (underToLaurent R) q w)
          (precompNode (BassMWholeNerve.coefficientModel P ((underToLaurent R).app b)) N))
          (CoefficientBassLaurentCompositionCarrier.family P q w r),
          NativeSquareFiveSimplex.parameter t)) =
      midpointProduct P p q w
        (lowerSurface P p (underToLaurent R) (laurentPlus_projection P b) t, r) :=
  lower_parameter_midpoint P p q w (underToLaurent R) (laurentPlus_projection P b)
    (laurentPlus_projection P d) (plus_lower_anchor P p q w) r t

/-- The inverse cell has the same binary clock and its separate original chart anchor. -/
theorem minus_lower_parameter (r t : I) :
    laurentPlacement P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
      (FiniteSourceSheet.laurent D F
        (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d))
        (CoefficientSquareFamilies.polynomialNodes P p)
        (mapParameter (fun N ↦ reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P
            (underToLaurentInvert R) q w)
          (precompNode (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app b)) N))
          (CoefficientBassLaurentCompositionCarrier.family P q w r),
          NativeSquareFiveSimplex.parameter t)) =
      midpointProduct P p q w
        (lowerSurface P p (underToLaurentInvert R) (laurentMinus_projection P b) t, r) :=
  lower_parameter_midpoint P p q w (underToLaurentInvert R) (laurentMinus_projection P b)
    (laurentMinus_projection P d) (minus_lower_anchor P p q w) r t

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
