/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeTripleLaurentAnchor

/-!
# Every source-whiskered old M node retains its frozen reference

Transport first by the old binary Laurent reference, then source-precompose, and finally use
the actual right-first triple input comparison. Reanchoring this whole Laurent node by the
canonical triple anchor gives the literal old precomposition node. Every point of its
139-simplex and the unchanged selected scalar cube follow from this dependent-node equality.
-/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.TripleLaurent
open BassH0Merge CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "Q" => BassProjectionPath.source P d
local notation "F" => BassProjectionPath.WholeReference.reference P d (input P p q r)
local notation "G" => BassProjectionPath.WholeReference.reference P d (precompInput P p q r)
local notation "H" => BassH0Diagram.reference P ((p ≫ q) ≫ r)
local notation "B" => BassOverlap.commonReference P q r

/-- The full binary node enters the triple Laurent reference by the three specified maps. -/
def precompLaurentNode (N : CommonReferenceNerve.Node B) : CommonReferenceNerve.Node F :=
  CommonReferenceProduct.reanchor (F₀ := F) (F₁ := G)
    (isoWhiskerRight (inputIso P p q r) (Q).functor)
    (precompNode A (CommonReferenceProduct.reanchor
      (BassMWholeConeCarrier.referenceIso P q r) N))

/-- The model morphism and its entire reference equal the literal frozen precomposition node. -/
theorem precompLaurentNode_anchor (N : CommonReferenceNerve.Node B) :
    CommonReferenceProduct.reanchor (anchor P p q r) (precompLaurentNode P p q r N) =
      CommonReferenceProduct.reanchor (BassMWholeNerve.precompAnchor P p q r)
        (precompNode (BassMWholeNerve.coefficientModel P p) N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change anchor P p q r ≪≫
      (isoWhiskerRight (inputIso P p q r) (Q).functor ≪≫
        isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor
          (BassMWholeConeCarrier.referenceIso P q r ≪≫ N.2)) =
    BassMWholeNerve.precompAnchor P p q r ≪≫
      isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor N.2
  rw [isoWhiskerLeft_trans]
  calc
    _ = ((anchor P p q r ≪≫
        isoWhiskerRight (inputIso P p q r) (Q).functor) ≪≫
          isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor
            (BassMWholeConeCarrier.referenceIso P q r)) ≪≫
        isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor N.2 := by
      simp only [Iso.trans_assoc]
    _ = _ := congrArg
      (fun e ↦ e ≪≫ isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor N.2)
      (anchor_join P p q r)

/-- Every original node retains its complete frozen reference and original insertion index. -/
theorem precomp_whole_nodes (i : Fin 140) :
    CommonReferenceProduct.reanchor (anchor P p q r)
        (precompLaurentNode P p q r (BassMWhole.nodes P q r i)) =
      BassMWholeNerve.precompNodes P p q r i :=
  precompLaurentNode_anchor P p q r (BassMWhole.nodes P q r i)

/-- Every point of the original 139-simplex follows the four actual full-node maps. -/
theorem precomp_whole_parameter (z : StdSimplex ℝ (Fin 140)) :
    mapParameter (CommonReferenceProduct.reanchor (anchor P p q r))
      (mapParameter (CommonReferenceProduct.reanchor (F₀ := F) (F₁ := G)
          (isoWhiskerRight (inputIso P p q r) (Q).functor))
        (mapParameter (precompNode A)
          (mapParameter (CommonReferenceProduct.reanchor
              (BassMWholeConeCarrier.referenceIso P q r))
            (CommonReferenceNerve.parameter B (BassMWhole.nodes P q r) z)))) =
      CommonReferenceNerve.parameter H (BassMWholeNerve.precompNodes P p q r) z := by
  rw [mapParameter_parameter, mapParameter_parameter]
  change mapParameter (CommonReferenceProduct.reanchor (anchor P p q r))
      (mapParameter (CommonReferenceProduct.reanchor (F₀ := F) (F₁ := G)
          (isoWhiskerRight (inputIso P p q r) (Q).functor))
        (CommonReferenceNerve.parameter G
          (fun i ↦ precompNode A (CommonReferenceProduct.reanchor
            (BassMWholeConeCarrier.referenceIso P q r) (BassMWhole.nodes P q r i))) z)) = _
  rw [mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N : Fin 140 → CommonReferenceNerve.Node H ↦
    CommonReferenceNerve.parameter H N z)
  funext i
  exact precomp_whole_nodes P p q r i

/-- The unchanged selected Laurent cube becomes the literal original precomposition lift. -/
theorem precomp_laurentCube (x y z : unitInterval) :
    mapParameter (CommonReferenceProduct.reanchor (anchor P p q r))
      (mapParameter (CommonReferenceProduct.reanchor (F₀ := F) (F₁ := G)
          (isoWhiskerRight (inputIso P p q r) (Q).functor))
        (mapParameter (precompNode A)
          (BassMWholeConeCarrier.laurentCube P q r (x, (y, z))))) =
      BassMWholeNerve.precompLift P p q r ![x, y, z] := by
  change mapParameter (CommonReferenceProduct.reanchor (anchor P p q r))
      (mapParameter (CommonReferenceProduct.reanchor (F₀ := F) (F₁ := G)
          (isoWhiskerRight (inputIso P p q r) (Q).functor))
        (mapParameter (precompNode A)
          (mapParameter (CommonReferenceProduct.reanchor
              (BassMWholeConeCarrier.referenceIso P q r))
            (CommonReferenceNerve.parameter B (BassMWhole.nodes P q r)
              (BassMWhole.scalarCube.{u} ![x, y, z]))))) =
    CommonReferenceNerve.parameter H (BassMWholeNerve.precompNodes P p q r)
      (BassMWhole.scalarCube.{u} ![x, y, z])
  exact precomp_whole_parameter P p q r _

end Quillen.PerfectComplexes.BassMWholeConeCarrier.TripleLaurent
