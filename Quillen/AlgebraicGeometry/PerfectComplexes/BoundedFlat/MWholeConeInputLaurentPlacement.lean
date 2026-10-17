/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentProduct
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeTripleLaurentAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomCommonFamily

/-! The input-cap Laurent product in the fixed right-first ordinary triple reference. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassH0Merge BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original M bottom anchor identifies the entire Laurent binary product reference. -/
def pairAnchor : (reference P d (inputReference P q w)).functor ≅
    (BassProjectionPath.source P b ≫
      CoefficientBassLaurentCompositionCarrier.reference P q w).functor :=
  referenceIso P q w ≪≫ BassBottomCommonFamily.referenceIso P q w

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The actual coefficient triple is source-precomposed by the unchanged full input reference. -/
abbrev fixedInput := E ≫ TripleLaurent.input P p q w

/-- The right-first normalization keeps its original scheme association and source whisker. -/
def rightInputIso : (fixedInput P p q w E).functor ≅
    ((E ≫ normalizedMap (coefficientMap P p)) ≫ inputReference P q w).functor :=
  isoWhiskerLeft E.functor (TripleLaurent.inputIso P p q w) ≪≫
    (Functor.associator E.functor (normalizedMap (coefficientMap P p)).functor
      (inputReference P q w).functor).symm

/-- Full placement keeps the original bottom anchor and every associator in their order. -/
def anchor : (reference P d (fixedInput P p q w E)).functor ≅
    (productReference P p q w E).functor :=
  isoWhiskerRight (rightInputIso P p q w E) (BassProjectionPath.source P d).functor ≪≫
    Functor.associator (E ≫ normalizedMap (coefficientMap P p)).functor
      (inputReference P q w).functor (BassProjectionPath.source P d).functor ≪≫
    isoWhiskerLeft (E ≫ normalizedMap (coefficientMap P p)).functor (pairAnchor P q w) ≪≫
    (Functor.associator (E ≫ normalizedMap (coefficientMap P p)).functor
      (BassProjectionPath.source P b).functor
      (CoefficientBassLaurentCompositionCarrier.reference P q w).functor).symm

/-- The entire product nerve is placed before any native evaluation. -/
def place : C(|parameterSSet (productReference P p q w E)|,
    |parameterSSet (reference P d (fixedInput P p q w E))|) :=
  mapParameter (CommonReferenceProduct.reanchor (anchor P p q w E))

/-- The first original height half now lies in the fixed triple Laurent reference. -/
def placedFamily :
    C(I × (FourEdgeTree.space E (normalizedMap (polynomialProjection P a)) × I),
      |parameterSSet (reference P d (fixedInput P p q w E))|) :=
  (place P p q w E).comp (family P p q w E)

/-- The full lower row retains the actual original Laurent source action. -/
theorem placedFamily_source (r : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    placedFamily P p q w E (r, (z, 0)) = place P p q w E
      (product P p q w E
        (FourEdge.TargetCone.laurent P p E (SSet.toTop.map (FourEdge.beta P a E) z), r)) :=
  congrArg (place P p q w E) (family_source P p q w E r z)

/-- The exact full midpoint target retains beta of the prescribed target tree map. -/
theorem placedFamily_target (r : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    placedFamily P p q w E (r, (z, 1)) = place P p q w E
      (product P p q w E
        (SSet.toTop.map (FourEdge.beta P b (E ≫ normalizedMap (coefficientMap P p)))
          (FourEdge.TargetSpan.treeMap P p E z), r)) :=
  congrArg (place P p q w E) (family_target P p q w E r z)

/-- Complete reference transport leaves the original Laurent-composition value unchanged. -/
theorem placedFamily_native (n : ℕ) (r s : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a)))
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P d (fixedInput P p q w E)) n
      (placedFamily P p q w E (r, (z, s))) x =
      (boundedFlatCoefficientLaurentCompositionHomotopy P q w).level n
        (r, (boundedFlatCoefficientBassComparisonHomotopy P p).level n
          (s, FourEdgeTree.nativeEval E (normalizedMap (polynomialProjection P a)) n z x)) :=
  (pointwise_reanchor (anchor P p q w E) n (family P p q w E (r, (z, s))) x).trans
    (family_native P p q w E n r s z x)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
