/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNativeCube
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierLaurentReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation

/-! The frozen original M cube retains its complete reference in the full Laurent cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The binary-normalization input reference for the coefficient maps of `q` and `p`. -/
abbrev inputReference :=
  BinaryNormalizationSimplex.sourceMap (coefficientMap P q) (coefficientMap P p)

/-- The actual old common reference is preserved by the original normalization isomorphism. -/
def referenceIso :
    (reference P c (inputReference P p q)).functor ≅
      (BassOverlap.commonReference P p q).functor :=
  CoefficientBassSeedCarrierLaurentReference.referenceIso P p q

/-- The selected original cube, without making another extension choice. -/
def laurentCube : C(I × (I × I),
    |nerve (Codiscrete (CommonReferenceNerve.Node
      (reference P c (inputReference P p q))))|) :=
  (mapParameter (CommonReferenceProduct.reanchor (referenceIso P p q))).comp
    ((CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
      (BassMWhole.nodes P p q)).comp
      ⟨fun z ↦ BassMWhole.scalarCube.{u} ![z.1, z.2.1, z.2.2], by fun_prop⟩)

/-- The complete native M cube is recovered at every degree and every independent coordinate. -/
theorem laurentCube_native (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (reference P c (inputReference P p q)) n
      (laurentCube P p q (r, (s, t))) x =
        (BassMWhole.interiorCube P p q).level n (r, (s, (t, x))) := by
  dsimp only [laurentCube, ContinuousMap.comp_apply]
  rw [pointwise_reanchor, pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  rfl

/-- Inclusion into the whole Laurent summand of the unreduced cone. -/
def cube : C(I × (I × I), FourEdge.scalarCone P c (inputReference P p q)) :=
  (FourEdgeTree.laurentInclusion (inputReference P p q)
    (BassH0Merge.normalizedMap (polynomialProjection P c))
    (reference P c (inputReference P p q))
    (FourEdge.beta P c (inputReference P p q))).comp (laurentCube P p q)

theorem cube_native (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P c (inputReference P p q) n (cube P p q (r, (s, t))) x =
      (LoopPrespectrum.mappingConeInclusion
        (boundedFlatCoefficientBassSquareComparison P c)).map n
        ((BassMWhole.interiorCube P p q).level n (r, (s, (t, x)))) := by
  dsimp only [cube, ContinuousMap.comp_apply]
  rw [FourEdge.coneEval_laurent]
  dsimp only [FourEdge.laurentValue]
  rw [laurentCube_native]

end Quillen.PerfectComplexes.BassMWholeConeCarrier
