/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskeredStart
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence

/-!
# The exact common terminal H0 component of the two whiskered cubes

The middle component of the original postcomposed cube and the first component of the
original precomposed cube retain the same full H0(v) nodes and the specified reference.
The proof uses the actual normalized pullback associativity equation, then all six original
primitive supports. Both selected scalar cubes and their asymmetric half/quarter speeds remain.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge
attribute [local irreducible] boundedFlatNormalizedPullback

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The actual post-middle anchor is one small transport of its two specified raw comparisons. -/
theorem terminal_post_anchor_small :
    postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.middleIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor =
      smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback (postcomp_total P u v w)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (coefficientMap P ((laurentUnderFunctor R).map w))
          (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)) ≪≫
        isoWhiskerRight
          (eqToIso (congrArg boundedFlatNormalizedPullback
              (BassH1References.middle_total P u v).symm) ≪≫
            boundedFlatNormalizedPullbackCompIso
              (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
              (coefficientMap P u))
          (boundedFlatNormalizedPullback (coefficientMap P ((laurentUnderFunctor R).map w)))) := by
  rw [postcomp_anchor_small, BassH1References.middleIso]
  erw [smallIso_postcomp]
  exact (smallIso_trans _ _).symm

/-- The actual pre-first anchor retains the same explicit geometric transport and comparison. -/
theorem terminal_pre_anchor_small :
    precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.firstIso P v w) =
      smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback (precomp_total P u v w)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
          (coefficientMap P u)) ≪≫
        isoWhiskerLeft (boundedFlatNormalizedPullback (coefficientMap P u))
          (eqToIso (congrArg boundedFlatNormalizedPullback
              (BassH1References.first_total P v w).symm) ≪≫
            boundedFlatNormalizedPullbackCompIso
              (coefficientMap P ((laurentUnderFunctor R).map w))
              (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b))) := by
  rw [precomp_anchor_small, BassH1References.firstIso]
  erw [smallIso_precomp]
  exact (smallIso_trans _ _).symm

/-- The post-middle and pre-first components have the same entire dependent reference anchor. -/
theorem whiskered_terminal_anchor :
    postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.middleIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.firstIso P v w) := by
  rw [terminal_post_anchor_small, terminal_pre_anchor_small]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using (anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
    (coefficientMap P u)
    (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
    _ (BassH1References.first_total P v w).symm
    (BassH1References.middle_total P u v).symm
    (precomp_total P u v w) (postcomp_total P u v w)).symm

/-- All 31 nodes retain both their original functor and their full reference isomorphism. -/
theorem whiskered_terminal_nodes (i : Fin 31) :
    postcompNodes P u v w (middleIndex i) = precompNodes P u v w (firstIndex i) := by
  unfold postcompNodes precompNodes
  rw [reanchor_postcomp_nodes _ _ (BassH1References.middleIso P u v) _ _ middleIndex
      (middle_nodes P u v) i,
    reanchor_precomp_nodes _ _ (BassH1References.firstIso P v w) _ _ firstIndex
      (first_nodes P v w) i,
    whiskered_terminal_anchor]
  simp only [ModelSimplex.reanchorNodes, CommonReferenceNerve.postcompNode,
    CommonReferenceNerve.precompNode, BassH1Components.middleNodes,
    BassH1Components.firstNodes]
  rfl

/-- The entire common terminal component keeps the original half/quarter-speed coordinates. -/
theorem whiskered_terminal_face (s t : unitInterval) :
    postcompLift P u v w ![1, upper s, upper (lower t)] =
      precompLift P u v w ![1, lower s, t] := by
  change CommonReferenceNerve.parameter _ (postcompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![1, upper s, upper (lower t)]) =
    CommonReferenceNerve.parameter _ (precompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![1, lower s, t])
  rw [BassMWhole.cube_one, BassMWhole.cube_one]
  change CommonReferenceNerve.parameter _ _
      (StdSimplex.map BassMWholeOrder.oldIndex
        (BassH1Order.h1Parameter.{u} (upper s, upper (lower t)))) =
    CommonReferenceNerve.parameter _ _
      (StdSimplex.map BassMWholeOrder.oldIndex (BassH1Order.h1Parameter.{u} (lower s, t)))
  rw [BassH1Order.h1_middle_cell, BassH1Order.h1_lower]
  change CommonReferenceNerve.parameter _ _
      (StdSimplex.map BassMWholeOrder.oldIndex
        (StdSimplex.map BassH1Order.middleIndex (BassH0Diagram.parameter (s, t)))) =
    CommonReferenceNerve.parameter _ _
      (StdSimplex.map BassMWholeOrder.oldIndex
        (StdSimplex.map BassH1Order.firstIndex (BassH0Diagram.parameter (s, t))))
  rw [← StdSimplex.map_comp, ← StdSimplex.map_comp]
  exact (h0_supported_parameter _ (postcompNodes P u v w)
    (fun i ↦ precompNodes P u v w (firstIndex i)) middleIndex
    (whiskered_terminal_nodes P u v w)
    BassMWholeOrder.oldMiddlePlus_monotone BassMWholeOrder.oldMiddleMinus_monotone s t).trans
      (h0_supported_parameter _ (precompNodes P u v w)
        (fun i ↦ precompNodes P u v w (firstIndex i)) firstIndex (fun _ ↦ rfl)
        BassMWholeOrder.oldFirstPlus_monotone BassMWholeOrder.oldFirstMinus_monotone s t).symm

end Quillen.PerfectComplexes.BassMWholeNerve
