/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeTripleLaurentAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgePrecompNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorNative

/-! The central input-cap cell is the unchanged original M cube on the coefficient input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "E" => inputReference P q w
local notation "F" => TripleLaurent.input P p q w

/-- Source precomposition and the original right-first triple normalization retain the old cap. -/
def carrierMap : C(FourEdge.scalarCone P d E, FourEdge.scalarCone P d F) :=
  (FourEdge.Reanchor.cone P d (A ≫ E) F (TripleLaurent.inputIso P p q w)).comp
    (FourEdge.Precomp.cone P d A E)

/-- The literal entire Laurent map exposes the same full reference route used by the old cube. -/
def laurentMap : C(|parameterSSet (reference P d E)|, |parameterSSet (reference P d F)|) :=
  (mapParameter (CommonReferenceProduct.reanchor
    (isoWhiskerRight (TripleLaurent.inputIso P p q w)
      (BassProjectionPath.source P d).functor))).comp
      (mapParameter (precompNode A))

theorem carrierMap_laurent (y : |parameterSSet (reference P d E)|) :
    carrierMap P p q w (FourEdgeTree.laurentInclusion E
      (normalizedMap (polynomialProjection P d)) (reference P d E) (FourEdge.beta P d E) y) =
      FourEdgeTree.laurentInclusion F (normalizedMap (polynomialProjection P d))
        (reference P d F) (FourEdge.beta P d F) (laurentMap P p q w y) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [FourEdge.Precomp.cone_laurent]
  exact FourEdge.Reanchor.cone_laurent P d (A ≫ E) F (TripleLaurent.inputIso P p q w) _

theorem carrierMap_tip :
    carrierMap P p q w (FourEdgeTree.tip E (normalizedMap (polynomialProjection P d))
      (reference P d E) (FourEdge.beta P d E)) =
      FourEdgeTree.tip F (normalizedMap (polynomialProjection P d))
        (reference P d F) (FourEdge.beta P d F) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [FourEdge.Precomp.cone_tip, FourEdge.Reanchor.cone_tip]

/-- The central whole cell retains the existing corrected cube at every original coordinate. -/
def family : C(I × (I × I), FourEdge.scalarCone P d F) :=
  (carrierMap P p q w).comp (corrected P q w)

theorem family_left (r t : I) :
    family P p q w (r, (0, t)) =
      FourEdgeTree.laurentInclusion F (normalizedMap (polynomialProjection P d))
        (reference P d F) (FourEdge.beta P d F)
        (laurentMap P p q w (laurentCube P q w (r, (0, t)))) := by
  change carrierMap P p q w (corrected P q w (r, (0, t))) = _
  rw [corrected_left]
  exact carrierMap_laurent P p q w _

theorem family_right (r t : I) :
    family P p q w (r, (1, t)) =
      FourEdgeTree.tip F (normalizedMap (polynomialProjection P d))
        (reference P d F) (FourEdge.beta P d F) := by
  change carrierMap P p q w (corrected P q w (r, (1, t))) = _
  rw [corrected_right]
  exact carrierMap_tip P p q w

/-- Native source precomposition acts on the actual coefficient input, including degree zero. -/
theorem carrierMap_native (n : ℕ) (z : FourEdge.scalarCone P d E)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d F n (carrierMap P p q w z) x =
      FourEdge.coneEval P d E n z ((prespectrumMap A).map n x) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  exact (FourEdge.Reanchor.cone_native P d (A ≫ E) F (TripleLaurent.inputIso P p q w)
    n (FourEdge.Precomp.cone P d A E z) x).trans
      (FourEdge.Precomp.cone_native P d A E n z x)

/-- The central cell is the original K evaluated on the unchanged target overlap. -/
theorem family_native (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d F n (family P p q w (r, (h, t))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P b).map n)
          (h, BassMWholeConeCarrier.input P (a := b) n t ((prespectrumMap A).map n x))) := by
  change FourEdge.coneEval P d F n (carrierMap P p q w (corrected P q w (r, (h, t)))) x = _
  rw [carrierMap_native, coneComposition_cylinder]

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
