/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopWord
public import Quillen.Aglib.Topology.Path.SpanReassociationPointwise
public import Quillen.Topology.Prespectrum.SpanReassociationEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# Native recovery of the original global span reassociation

The whole original vertex top determines every one of the five native leaves. Pointwise
naturality therefore recovers the prescribed three-stage reassociation at every original
level and input, without requiring continuity of evaluation on the entire reference nerve.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.NativePathCells
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopAssoc
open InputCompositionTopWord
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The existing pointwise evaluation, restricted below to the actual compact carrier faces. -/
def ev (n : ℕ) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n)
    (z : InputCompositionCarrierCharts.Carrier f g) :=
  CommonReferenceNerve.pointwisePrespectrumFamily (InputCompositionCarrierCharts.source f g) n z x

/-- The prescribed original five-piece relative comparison of the actual raw span maps. -/
def reassociationNative := HomotopyPushout.identicalLegCompositionPasting
  (boundedFlatPerfectPrespectrumMap (projection.app Z))
  (boundedFlatPerfectPrespectrumMap (projection.app Y))
  (boundedFlatPerfectPrespectrumMap (projection.app X))
  (boundedFlatPerfectPrespectrumMap g)
  (boundedFlatPerfectPrespectrumMap (polynomial.map g))
  (boundedFlatPerfectPrespectrumMap f)
  (boundedFlatPerfectPrespectrumMap (polynomial.map f))
  (polynomialSquareHomotopy g) (polynomialSquareHomotopy f)

/-- Every point of the whole original vertex top is the actual pasted span cylinder. -/
theorem pasted_native (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) (t : unitInterval) :
    ev f g n x (pastedTop f g t) =
      (comparison X).map n ((reassociationNative f g).level n (1, (t, x))) := by
  rw [pastedTop_apply]
  refine (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputCompositionCarrierCharts.source f g) (InputCompositionTopVertex.face f g)
    n (1, t) x).trans ?_
  refine (InputCompositionTopVertex.face_native f g n 1 t x).trans ?_
  change (comparison X).map n ((InputCompositionSpan.homotopy f g).level n
    (lower 1, HomotopyPushout.cylinder
      (boundedFlatPerfectPrespectrumMap (projection.app Z))
      (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x))) = _
  rw [InputCompositionSpan.homotopy_cylinder_lower]
  exact congrArg ((comparison X).map n)
    (((InputCompositionSpan.movingSquare f g).at_one n t x).trans
      (((reassociationNative f g).level n).apply_one (t, x)).symm)

/-- Whole target-word recovery forces all original reassociation stages and their two clocks. -/
theorem reassociation_native (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n)
    (r s : unitInterval) :
    ev f g n x (reassociation f g (r, s)) =
      (comparison X).map n ((reassociationNative f g).level n (r, (s, x))) := by
  let a := boundedFlatPerfectPrespectrumMap g
  let c := boundedFlatPerfectPrespectrumMap f
  let d := boundedFlatPerfectPrespectrumMap (polynomial.map f)
  let h := boundedFlatPerfectPrespectrumMap (projection.app X)
  let j := boundedFlatPerfectPrespectrumMap (projection.app Y)
  let H := polynomialSquareHomotopy g
  let K := polynomialSquareHomotopy f
  let iL := HomotopyPushout.inl h h
  let iR := HomotopyPushout.inr h h
  let P := H.postcomp (d ≫ iL)
  let Q : Homotopy ((a ≫ j) ≫ (d ≫ iL)) ((a ≫ c) ≫ (h ≫ iL)) :=
    (Homotopy.precomp a (K.postcomp iL)).cast
      (by simp only [d, h, j, Category.assoc]) (by simp only [c, h, Category.assoc])
  let T := Homotopy.precomp (a ≫ c) (HomotopyPushout.glue h h)
  let U : Homotopy ((a ≫ c) ≫ (h ≫ iR)) ((a ≫ j) ≫ (d ≫ iR)) :=
    (Homotopy.precomp a (K.symm.postcomp iR)).cast
      (by simp only [c, h, Category.assoc]) (by simp only [d, h, j, Category.assoc])
  let V := H.symm.postcomp (d ≫ iR)
  have hn (t v : unitInterval) :
      Path.Homotopy.spanReassociation (P.path n x) (Q.path n x) (T.path n x)
        (U.path n x) (V.path n x) (t, v) =
      (reassociationNative f g).level n (t, (v, x)) := by
    exact Quillen.NativeSpanReassociation.word n x id
      (P.path n x) (Q.path n x) (T.path n x) (U.path n x) (V.path n x)
      P Q T U V (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl) t v
  have ht (v : unitInterval) :
      ev f g n x (pastedTop f g v) = (comparison X).map n
        ((((P.path n x).trans (Q.path n x)).trans
          ((T.path n x).trans ((U.path n x).trans (V.path n x)))) v) := by
    have htop := hn 1 v
    rw [ContinuousMap.HomotopyWith.apply_one] at htop
    exact (pasted_native f g n x v).trans (congrArg ((comparison X).map n) htop.symm)
  exact (Path.Evaluation.spanReassociation_of_target_function (ev f g n x)
    ((comparison X).map n)
    (firstPlus f g) (lastPlus f g) (overlapTop f g) (lastMinus f g).symm (firstMinus f g).symm
    (P.path n x) (Q.path n x) (T.path n x) (U.path n x) (V.path n x) ht r s).trans
      (congrArg ((comparison X).map n) (hn r s))

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopAssoc
