/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexNativeCells

/-! Actual normalized common references for all three original M vertex-stage components. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMReferences
open BassReferenceMerge BassMComponents
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

include hc in
/-- The original chart projection equation identifies the actual moving-square total. -/
theorem moving_total : coefficientMap P (α.app c) ≫
    (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  rw [← Category.assoc (coefficientMap P (α.app c)) (polynomialProjection P c), hc]

/-- The moving component's anchor uses its actual normalized pullback composition iso. -/
def movingIso : (BassOverlap.commonReference P u v).functor ≅
    (polynomialSource P u v ≫ BassH0Merge.normalizedMap (coefficientMap P (α.app c))).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (moving_total P u v α hc).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso (coefficientMap P (α.app c))
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u))

/-- Every original moving-square node retains its full reference under the actual chart map. -/
def movingNodes (i : Fin 18) : BassOverlap.Node P u v :=
  BassH1Join.postReferenceNode (BassOverlap.commonReference P u v)
    (BassH0Merge.normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc)
    (polynomialNodes P u v i)

/-- The whole reanchored diagram is precisely the original native chart-postcomposed square. -/
theorem moving_original : ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (movingNodes P u v α hc i).1) (fun i ↦ (movingNodes P u v α hc i).2) =
    (polynomialSimplex P u v).postcomp
      (BassH0Merge.normalizedMap (coefficientMap P (α.app c))) := by
  unfold movingNodes BassH1Join.postReferenceNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (BassH1Components.postcompose_reference (polynomialSource P u v)
    (fun i ↦ (polynomialNodes P u v i).1) (fun i ↦ (polynomialNodes P u v i).2)
    (BassH0Merge.normalizedMap (coefficientMap P (α.app c)))).symm

/-- The original middle product uses the same Laurent/projection total as all fixed faces. -/
theorem middle_total : (laurentPlus P c ≫ polynomialProjection P c) ≫
    (coefficientMap P v ≫ coefficientMap P u) =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  rw [laurentPlus_projection]

/-- The middle product retains its actual positive projection source before reference transport. -/
def middleIso : (BassOverlap.commonReference P u v).functor ≅
    (coefficientSource P u v ≫ BassProjectionPath.source P c).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (middle_total P u v).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso (laurentPlus P c ≫ polynomialProjection P c)
      (coefficientMap P v ≫ coefficientMap P u))

/-- Every original product vertex and reference is retained, without identifying endpoints. -/
def middleNodes (i : Fin 15) : BassOverlap.Node P u v :=
  BassH1Join.reanchoredProductNode (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (fun i ↦ (coefficientNodes P u v i).1)
    (fun i ↦ (coefficientNodes P u v i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) (middleIso P u v) i

/-- The entire middle family remains the actual original independently varying composition. -/
theorem middle_original : ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (middleNodes P u v i).1) (fun i ↦ (middleNodes P u v i).2) =
      middleSimplex P u v :=
  ModelSimplex.ofIsos_change_reference (middleIso P u v) _ _

end Quillen.PerfectComplexes.BassMReferences
