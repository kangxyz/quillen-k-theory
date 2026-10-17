/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeGeometricCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReference
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! The exact original Laurent reference enters the whole two-chart reference by normalization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedCarrierLaurentReference
open BassH0Merge CommonReferenceNerve CoefficientBassNegativeCarrierReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The input reference retains the literal coefficient composite of the existing carrier. -/
abbrev inputReference := normalizedMap (coefficientMap P q ≫ coefficientMap P p)

/-- The complete original normalization supplies the shared Laurent reference isomorphism. -/
def referenceIso :
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)).functor ≅
      (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q).functor :=
  (BinaryNormalizationSimplex.total
    (laurentPlus P c ≫ polynomialProjection P c)
    (coefficientMap P q ≫ coefficientMap P p)).symm ≪≫
      eqToIso (congrArg (fun f ↦ (normalizedMap f).functor)
        (congrArg (fun f ↦ f ≫ (coefficientMap P q ≫ coefficientMap P p))
          (laurentPlus_projection P c)))

/-- Every dependent Laurent node keeps its original model map and full new reference. -/
def nodeMap : Node (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) →
    Node (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) :=
  CommonReferenceProduct.reanchor (referenceIso P p q)

/-- The whole realization is transported, rather than just its evaluated endpoint. -/
def parameterMap := mapParameter (nodeMap P p q)

/-- Native evaluation is retained on the whole Laurent nerve at every level. -/
theorem parameterMap_native (n : ℕ)
    (y : |nerve (Codiscrete
      (Node (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q)))|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily
        (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) n
        (parameterMap P p q y) x =
      pointwisePrespectrumFamily
        (CoefficientBassPositiveC1BoundaryLift.laurentReference P p q) n y x :=
  pointwise_reanchor (referenceIso P p q) n y x

end Quillen.PerfectComplexes.CoefficientBassSeedCarrierLaurentReference
