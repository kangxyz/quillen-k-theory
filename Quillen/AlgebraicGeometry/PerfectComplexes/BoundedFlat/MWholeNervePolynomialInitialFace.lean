/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseOuterEndpoints

/-!
# The initial polynomial e0 face is the old postcomposed first-stage M face

The scalar square here is the original moving square at pause time zero. It is not the
paused terminal square. Every reference equality precedes the three-support transfer.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join

/-- The original first-stage moving component, with its original order retained. -/
def initialPolynomialIndex (inverse : Bool) : Fin 18 → Fin 140 :=
  BassMWholeOrder.vertexIndex ∘
    (if inverse then BassMVertexOrder.minusIndex else BassMVertexOrder.plusIndex)

/-- Only the original three primitive rectangles are transported into the old whole family. -/
theorem initial_polynomial_monotone (inverse : Bool) (i : Fin 3) :
    Monotone (initialPolynomialIndex inverse ∘
      (BassPrimitiveSupport.rectangleFace i).toOrderHom) := by
  cases inverse
  · exact BassMWholeOrder.vertexPlus_monotone i
  · exact BassMWholeOrder.vertexMinus_monotone i

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The actual chart endpoint2 total and the original moving/postcomp anchors agree.
This is equality of their specified isomorphisms, not merely the associated functors. -/
theorem polynomial_initial_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    polynomialFixedSideAnchor P u v w α hc 0 =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassMReferences.movingIso P u v α hc)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  rw [polynomialFixedSideAnchor, polynomialProductAnchor, postcomp_anchor_small,
    BassMReferences.movingIso]
  erw [smallIso_precomp, smallIso_postcomp]
  change smallIso _ ≪≫ smallIso
    (isoWhiskerLeft
      (boundedFlatNormalizedPullback
        (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u))
      (boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app c)))) = _
  have hraw := anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w)) (coefficientMap P (α.app c))
    (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c))
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) _ rfl
    (BassMReferences.moving_total P u v α hc).symm
    (polynomialProductTotal P u v w α hc).symm (postcomp_total P u v w)
  simpa only [eqToIso_refl, Iso.refl_trans, smallIso_trans, Iso.trans_assoc]
    using congrArg smallIso hraw

/-- Full Sigma equality with alpha(c), Laurent(w), the endpoint total and both old anchors. -/
theorem polynomial_initial_reference_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 18) :
    polynomialOuterNodes P u v w α hc 0 i =
      anchorNode (postcompAnchor P u v w)
        (CommonReferenceNerve.postcompNode
          (coefficientModel P ((laurentUnderFunctor R).map w))
          (BassMReferences.movingNodes P u v α hc i)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change polynomialFixedSideAnchor P u v w α hc 0 ≪≫
    isoWhiskerRight (movingSquareNodes P (polynomialUnderCoefficient R) u v i).2
      (CoefficientSquareFamilies.chartNodes P w α 2).1.functor = _
  rw [polynomial_initial_anchor]
  simp only [anchorNode, CommonReferenceNerve.postcompNode, BassMReferences.movingNodes,
    postReferenceNode, isoWhiskerRight_trans, Iso.trans_assoc]
  rfl

/-- Every actual old moving component node retains its full reference after postcomposition. -/
theorem initial_polynomial_plus_nodes (i : Fin 18) :
    postcompNodes P u v w (initialPolynomialIndex false i) =
      polynomialOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P c) 0 i := by
  rw [polynomial_initial_reference_nodes]
  unfold postcompNodes ModelSimplex.reanchorNodes
  change anchorNode (postcompAnchor P u v w)
    (CommonReferenceNerve.postcompNode (coefficientModel P ((laurentUnderFunctor R).map w))
      (BassMWhole.nodes P u v (initialPolynomialIndex false i))) = _
  unfold initialPolynomialIndex
  simp only [Bool.false_eq_true, ite_false, Function.comp_apply]
  rw [BassMWhole.vertex_nodes, BassMVertex.plus_nodes]

/-- Every actual old moving component node retains its full reference after postcomposition. -/
theorem initial_polynomial_minus_nodes (i : Fin 18) :
    postcompNodes P u v w (initialPolynomialIndex true i) =
      polynomialOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c) 0 i := by
  rw [polynomial_initial_reference_nodes]
  unfold postcompNodes ModelSimplex.reanchorNodes
  change anchorNode (postcompAnchor P u v w)
    (CommonReferenceNerve.postcompNode (coefficientModel P ((laurentUnderFunctor R).map w))
      (BassMWhole.nodes P u v (initialPolynomialIndex true i))) = _
  unfold initialPolynomialIndex
  simp only [ite_true, Function.comp_apply]
  rw [BassMWhole.vertex_nodes, BassMVertex.minus_nodes]

/-- The exact old first-stage moving surface is used only on its supported rectangles. -/
theorem initial_polynomial_plus_parameter {V W : Model.{u + 1}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (q t : unitInterval) :
    CommonReferenceNerve.parameter F N
      (BassMWhole.scalarCube.{u} ![lower q, 1, lower t]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (initialPolynomialIndex false i))
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, t)) := by
  rw [BassMWhole.cube_top]
  refine (congrArg (CommonReferenceNerve.parameter F N)
    (BassMScalarPasting.parameter_lower.{u} BassMWholeOrder.vertexIndex
      BassMWholeOrder.oldIndex BassMWhole.indexEqualities q (lower t))).trans ?_
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.vertexIndex
      (BassMVertexOrder.parameter.{u} (q, lower t))) = _
  rw [BassMVertexOrder.parameter_plus]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.vertexIndex
      (StdSimplex.map BassMVertexOrder.plusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, t)))) = _
  rw [← StdSimplex.map_comp]
  obtain ⟨i, z, hz⟩ := Quillen.ParameterSupport.collapsed_in
    BassPrimitiveSupport.coefficient_boundary_in (q, t)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i).toOrderHom z =
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, t) at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _ (initialPolynomialIndex false)
    (fun _ ↦ rfl) (BassPrimitiveSupport.rectangleFace i)
    (initial_polynomial_monotone false i) z

/-- The exact old first-stage moving surface is used only on its supported rectangles. -/
theorem initial_polynomial_minus_parameter {V W : Model.{u + 1}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (q t : unitInterval) :
    CommonReferenceNerve.parameter F N
      (BassMWhole.scalarCube.{u} ![lower q, 1, upper (upper t)]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (initialPolynomialIndex true i))
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm t)) := by
  rw [BassMWhole.cube_top]
  refine (congrArg (CommonReferenceNerve.parameter F N)
    (BassMScalarPasting.parameter_lower.{u} BassMWholeOrder.vertexIndex
      BassMWholeOrder.oldIndex BassMWhole.indexEqualities q (upper (upper t)))).trans ?_
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.vertexIndex
      (BassMVertexOrder.parameter.{u} (q, upper (upper t)))) = _
  rw [BassMVertexOrder.parameter_minus]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.vertexIndex
      (StdSimplex.map BassMVertexOrder.minusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm t)))) = _
  rw [← StdSimplex.map_comp]
  obtain ⟨i, z, hz⟩ := Quillen.ParameterSupport.collapsed_in
    BassPrimitiveSupport.coefficient_boundary_in (q, unitInterval.symm t)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i).toOrderHom z =
    DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm t) at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _ (initialPolynomialIndex true)
    (fun _ ↦ rfl) (BassPrimitiveSupport.rectangleFace i)
    (initial_polynomial_monotone true i) z

/-- Initial e0 equals the literal old postcomp first-stage face at its original speeds. -/
theorem polynomial_outer_initial_plus (q t : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P c) 0
      ![0, q, t] = postcompLift P u v w ![lower q, 1, lower t] := by
  change CommonReferenceNerve.parameter _
    (polynomialOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P c) 0)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
      ![0, q, t]) =
    CommonReferenceNerve.parameter _ (postcompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![lower q, 1, lower t])
  rw [ChangedBoundaryPause.cube_zero, initial_polynomial_plus_parameter]
  change CommonReferenceNerve.parameter _ _
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, t)) = _
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦
      CommonReferenceNerve.parameter _ N
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, t)))
  funext i
  exact (initial_polynomial_plus_nodes P u v w i).symm

/-- Initial e0 equals the literal old postcomp first-stage face at its original speeds. -/
theorem polynomial_outer_initial_minus (q t : unitInterval) :
    polynomialOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P c) 0
      ![0, q, unitInterval.symm t] = postcompLift P u v w ![lower q, 1, upper (upper t)] := by
  change CommonReferenceNerve.parameter _
    (polynomialOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c) 0)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
      ![0, q, unitInterval.symm t]) =
    CommonReferenceNerve.parameter _ (postcompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![lower q, 1, upper (upper t)])
  rw [ChangedBoundaryPause.cube_zero, initial_polynomial_minus_parameter]
  change CommonReferenceNerve.parameter _ _
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm t)) = _
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦
      CommonReferenceNerve.parameter _ N
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm t)))
  funext i
  exact (initial_polynomial_minus_nodes P u v w i).symm

end Quillen.PerfectComplexes.BassMWholeNerve
