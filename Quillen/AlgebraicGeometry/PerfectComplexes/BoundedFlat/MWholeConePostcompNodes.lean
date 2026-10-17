/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePostcompAnchor

/-! All 140 original M nodes survive the actual ordinary-cone postcomposition route. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
open BassH0Merge CommonReferenceNerve BassProjectionPath.WholeReference
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => inputReference P p q
local notation "F" => reference P d (input P p q w)
local notation "G" => BassOverlap.commonReference P p q
local notation "H" => BassH0Diagram.reference P ((p ≫ q) ≫ w)
local notation "L" => FourEdge.Target.sourcePost P w

/-- The whole node follows the actual old reference, coefficient action and left-first reanchor. -/
def postcompLaurentNode (N : CommonReferenceNerve.Node G) : CommonReferenceNerve.Node F :=
  CommonReferenceProduct.reanchor
    (isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor)
    (FourEdge.TargetCone.sourceNode P w E
      (CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q) N))

/-- The model arrow and complete anchor equal the unchanged frozen postcomposition node. -/
theorem postcompLaurentNode_anchor (N : CommonReferenceNerve.Node G) :
    CommonReferenceProduct.reanchor (TripleLaurent.anchor P p q w)
        (postcompLaurentNode P p q w N) =
      CommonReferenceProduct.reanchor (BassMWholeNerve.postcompAnchor P p q w)
        (postcompNode (BassMWholeNerve.coefficientModel P ((laurentUnderFunctor R).map w)) N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change TripleLaurent.anchor P p q w ≪≫
    (isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor ≪≫
      ((FourEdge.Target.terminalBoundaryAnchor P w E).symm ≪≫
        (FourEdge.Target.sourceBoundaryAnchor P w E ≪≫
          isoWhiskerRight (BassMWholeConeCarrier.referenceIso P p q ≪≫ N.2) (L).functor))) =
    BassMWholeNerve.postcompAnchor P p q w ≪≫ isoWhiskerRight N.2 (L).functor
  rw [isoWhiskerRight_trans]
  calc
    _ = ((((TripleLaurent.anchor P p q w ≪≫
        isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor) ≪≫
        (FourEdge.Target.terminalBoundaryAnchor P w E).symm) ≪≫
        FourEdge.Target.sourceBoundaryAnchor P w E) ≪≫
        isoWhiskerRight (BassMWholeConeCarrier.referenceIso P p q) (L).functor) ≪≫
      isoWhiskerRight N.2 (L).functor := by simp only [Iso.trans_assoc]
    _ = _ := congrArg (fun e ↦ e ≪≫ isoWhiskerRight N.2 (L).functor)
      (actual_anchor_join P p q w)

/-- Every original insertion index retains its complete model and reference isomorphism. -/
theorem postcomp_whole_nodes (i : Fin 140) :
    CommonReferenceProduct.reanchor (TripleLaurent.anchor P p q w)
        (postcompLaurentNode P p q w (BassMWhole.nodes P p q i)) =
      BassMWholeNerve.postcompNodes P p q w i :=
  postcompLaurentNode_anchor P p q w (BassMWhole.nodes P p q i)

/-- Every point of the original characteristic simplex follows the same full carrier route. -/
theorem postcomp_whole_parameter (z : StdSimplex ℝ (Fin 140)) :
    mapParameter (CommonReferenceProduct.reanchor (TripleLaurent.anchor P p q w))
      (laurentMap P p q w
        (mapParameter (CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q))
          (CommonReferenceNerve.parameter G (BassMWhole.nodes P p q) z))) =
    CommonReferenceNerve.parameter H (BassMWholeNerve.postcompNodes P p q w) z := by
  change mapParameter (CommonReferenceProduct.reanchor (TripleLaurent.anchor P p q w))
      (mapParameter (CommonReferenceProduct.reanchor
        (isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor))
        (mapParameter (FourEdge.TargetCone.sourceNode P w E)
          (mapParameter (CommonReferenceProduct.reanchor
            (BassMWholeConeCarrier.referenceIso P p q))
            (CommonReferenceNerve.parameter G (BassMWhole.nodes P p q) z)))) = _
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns : Fin 140 → CommonReferenceNerve.Node H ↦
    CommonReferenceNerve.parameter H ns z)
  funext i
  exact postcomp_whole_nodes P p q w i

/-- The selected original scalar cube becomes exactly the frozen postcomposition lift. -/
theorem postcomp_laurentCube (r s t : I) :
    mapParameter (CommonReferenceProduct.reanchor (TripleLaurent.anchor P p q w))
      (laurentMap P p q w (BassMWholeConeCarrier.laurentCube P p q (r, (s, t)))) =
      BassMWholeNerve.postcompLift P p q w ![r, s, t] :=
  postcomp_whole_parameter P p q w (BassMWhole.scalarCube.{u} ![r, s, t])

end Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
