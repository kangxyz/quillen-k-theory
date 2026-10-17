/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputCentral

/-! Whole polynomial and Laurent parameter maps agree at the original fourth source node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The full polynomial nerve has the prescribed right-first parameter at the old endpoint. -/
theorem polynomial_parameter4 (y : |parameterSSet (pairReference P q w)|) :
    polynomialPlacement P p q w
      (FiniteSourceSheet.polynomial (sourceReference P p) (pairReference P q w)
        (CoefficientSquareFamilies.polynomialNodes P p) (y, NativeSquareFiveSimplex.parameter 1)) =
    mapParameter (CommonReferenceProduct.reanchor
      (isoWhiskerRight (TripleLaurent.inputIso P p q w)
        (normalizedMap (polynomialProjection P d)).functor))
      (mapParameter (precompNode (normalizedMap (coefficientMap P p)))
        (PairProjection.polynomial P q w y)) := by
  rw [Path.target]
  unfold FiniteSourceSheet.polynomial
  rw [FiniteParameter.parameter_vertex]
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter (pairReference P q w) y
  dsimp only [polynomialPlacement, PairProjection.polynomial]
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter
    (input P p q w ≫ normalizedMap (polynomialProjection P d)) N z)
  funext i
  exact polynomial_node4 P p q w (ns i)

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)

/-- Every Laurent parameter, including nodes outside the attachment image, has the same anchor. -/
theorem laurent_parameter4
    (y : |parameterSSet (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d))|) :
    laurentPlacement P p q w β hd
      (FiniteSourceSheet.laurent (sourceReference P p) (pairReference P q w)
        (BassMWholeNerve.coefficientModel P (β.app d))
        (CoefficientSquareFamilies.polynomialNodes P p) (y, NativeSquareFiveSimplex.parameter 1)) =
    InputCentral.laurentMap P p q w (PairProjection.laurent P q w β hd y) := by
  rw [Path.target]
  unfold FiniteSourceSheet.laurent
  rw [FiniteParameter.parameter_vertex]
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter
    (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d)) y
  dsimp only [laurentPlacement, InputCentral.laurentMap, PairProjection.laurent,
    ContinuousMap.comp_apply]
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter
    (BassProjectionPath.WholeReference.reference P d (input P p q w)) N z)
  funext i
  exact laurent_node4 P p q w β hd (ns i)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
