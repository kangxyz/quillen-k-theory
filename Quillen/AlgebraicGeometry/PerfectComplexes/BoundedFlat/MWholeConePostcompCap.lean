/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorRealization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackSimplex

/-! The unchanged ordinary M cap followed by the actual target map in the fixed triple reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "f" => coefficientMap P w
local notation "g" => coefficientMap P q
local notation "h" => coefficientMap P p
local notation "E" => inputReference P p q

/-- The same normalized triple reference used by the prescribed three original comparisons. -/
abbrev input := NormalizedTripleSimplex.sourceMap f g h

/-- The actual input after the ordinary target action on the old binary carrier. -/
abbrev mappedInput := E ≫ normalizedMap f

/-- Only the small-model presentation of the original left-first target changes. -/
theorem mappedInput_functor : (mappedInput P p q w).functor =
    (NormalizedTripleSimplex.leftMap f g h).functor := rfl

/-- The original left-first normalization is retained with its full reference direction. -/
def inputIso : (input P p q w).functor ≅ (mappedInput P p q w).functor :=
  NormalizedTripleSimplex.leftFirst f g h ≪≫
    eqToIso (mappedInput_functor P p q w).symm

/-- First the actual coefficient cone map, then the exact normalized triple input reanchor. -/
def carrierMap : C(FourEdge.scalarCone P c E, FourEdge.scalarCone P d (input P p q w)) :=
  (FourEdge.Reanchor.cone P d (mappedInput P p q w) (input P p q w)
    (inputIso P p q w)).comp (FourEdge.TargetCone.coneMap P w E)

/-- The full Laurent map retains both the actual coefficient action and left-first reanchor. -/
def laurentMap : C(|parameterSSet (reference P c E)|,
    |parameterSSet (reference P d (input P p q w))|) :=
  (mapParameter (CommonReferenceProduct.reanchor
    (isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor))).comp
      (FourEdge.TargetCone.laurent P w E)

/-- The whole Laurent inclusion is transported before any native evaluation. -/
theorem carrierMap_laurent (y : |parameterSSet (reference P c E)|) :
    carrierMap P p q w (FourEdgeTree.laurentInclusion E
      (normalizedMap (polynomialProjection P c)) (reference P c E) (FourEdge.beta P c E) y) =
    FourEdgeTree.laurentInclusion (input P p q w) (normalizedMap (polynomialProjection P d))
      (reference P d (input P p q w)) (FourEdge.beta P d (input P p q w))
      (laurentMap P p q w y) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [FourEdge.TargetCone.coneMap_laurent]
  change FourEdge.Reanchor.cone P d (mappedInput P p q w) (input P p q w)
    (inputIso P p q w) (FourEdgeTree.laurentInclusion (mappedInput P p q w)
      (normalizedMap (polynomialProjection P d)) (reference P d (mappedInput P p q w))
      (FourEdge.beta P d (mappedInput P p q w)) (FourEdge.TargetCone.laurent P w E y)) = _
  exact FourEdge.Reanchor.cone_laurent P d (mappedInput P p q w) (input P p q w)
    (inputIso P p q w) (FourEdge.TargetCone.laurent P w E y)

/-- The original corrected M cube is not replaced or reparameterized. -/
def cap : C(I × (I × I), FourEdge.scalarCone P d (input P p q w)) :=
  (carrierMap P p q w).comp (corrected P p q)

/-- The whole original lower null word keeps every internal clock. -/
theorem cap_zero (s t : I) :
    cap P p q w (0, (s, t)) = carrierMap P p q w (lowerPath P p q s t) :=
  congrArg (carrierMap P p q w) (corrected_zero P p q s t)

/-- The whole original corrected upper word keeps its chosen nested concatenation. -/
theorem cap_one (s t : I) :
    cap P p q w (1, (s, t)) = carrierMap P p q w (correctedUpper P p q s t) :=
  congrArg (carrierMap P p q w) (corrected_one P p q s t)

/-- Height zero retains the complete original Laurent cube, including its full anchor. -/
theorem cap_left (r t : I) :
    cap P p q w (r, (0, t)) = carrierMap P p q w (cube P p q (r, (0, t))) :=
  congrArg (carrierMap P p q w) (corrected_left P p q r t)

/-- The height-zero Laurent face exposes its exact whole reference route. -/
theorem cap_left_laurent (r t : I) :
    cap P p q w (r, (0, t)) =
      FourEdgeTree.laurentInclusion (input P p q w) (normalizedMap (polynomialProjection P d))
        (reference P d (input P p q w)) (FourEdge.beta P d (input P p q w))
        (laurentMap P p q w (laurentCube P p q (r, (0, t)))) := by
  rw [cap_left]
  exact carrierMap_laurent P p q w (laurentCube P p q (r, (0, t)))

/-- Both constituent maps preserve the one original ordinary cone tip. -/
theorem carrierMap_tip :
    carrierMap P p q w (FourEdgeTree.tip E (normalizedMap (polynomialProjection P c))
      (reference P c E) (FourEdge.beta P c E)) =
    FourEdgeTree.tip (input P p q w) (normalizedMap (polynomialProjection P d))
      (reference P d (input P p q w)) (FourEdge.beta P d (input P p q w)) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [FourEdge.TargetCone.coneMap_tip, FourEdge.Reanchor.cone_tip]

/-- The entire terminal-height face is the same fixed target tip. -/
theorem cap_right (r t : I) :
    cap P p q w (r, (1, t)) =
      FourEdgeTree.tip (input P p q w) (normalizedMap (polynomialProjection P d))
        (reference P d (input P p q w)) (FourEdge.beta P d (input P p q w)) := by
  change carrierMap P p q w (corrected P p q (r, (1, t))) = _
  rw [corrected_right]
  exact carrierMap_tip P p q w

end Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
