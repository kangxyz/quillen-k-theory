/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0PolynomialEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSecondTargetNodes

/-!
# Polynomial nodes for the two original left-route constituents

Both five-node families are restrictions of the original M polynomial diagram transported
to the fixed C0/C1 polynomial reference. Their complete reference anchors, attachments, and
polynomial endpoint nodes are retained. No unit-intertwining or whole seed seam is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialNodes
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment

private theorem anchor_pre_cancel {V W T : Model.{v}} (K : V ⟶ T) (J : V ⟶ W)
    {H : W ⟶ T} (θ : K.functor ≅ (J ≫ H).functor) (N : Node H) :
    anchorNode θ.symm (preReferenceNode K J θ N) = precompNode J N := by
  rcases N with ⟨L, ρ⟩
  simp only [anchorNode, preReferenceNode, precompNode, ← Iso.trans_assoc,
    Iso.symm_self_id, Iso.refl_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual first moving-square reference, before transport to the fixed carrier. -/
def firstBaseAnchor : (BassMComponents.polynomialSource P p q).functor ≅
    (CoefficientSquareFamilies.polynomialSource P p ≫
      normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q))).functor :=
  CoefficientMovingSquareRows.firstAnchor
    (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm

/-- The actual second moving-square reference, before the same fixed transport. -/
def secondBaseAnchor : (BassMComponents.polynomialSource P p q).functor ≅
    (normalizedMap (coefficientMap P p) ≫
      CoefficientSquareFamilies.polynomialSource P q).functor :=
  CoefficientMovingSquareRows.secondAnchor
    (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm

/-- The first family keeps the original postcomposition anchor after polynomial transport. -/
def firstAnchor : (polynomialReference P p q).functor ≅
    (CoefficientSquareFamilies.polynomialSource P p ≫
      normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q))).functor :=
  (BassMOuterJoin.movingSideBaseIso P p q).symm ≪≫ firstBaseAnchor P p q

/-- The second family keeps the original precomposition anchor after polynomial transport. -/
def secondAnchor : (polynomialReference P p q).functor ≅
    (normalizedMap (coefficientMap P p) ≫
      CoefficientSquareFamilies.polynomialSource P q).functor :=
  (BassMOuterJoin.movingSideBaseIso P p q).symm ≪≫ secondBaseAnchor P p q

/-- The first unchanged five-node word is `[5, 7, 17, 6, 13]`. -/
def firstNodes (i : Fin 5) : Node (polynomialReference P p q) :=
  transportPolynomialNode P p q
    (BassMComponents.polynomialNodes P p q (BassMOuterJoin.firstTargetWordIndex i))

/-- The second unchanged five-node word is `[9, 12, 13, 10, 11]`. -/
def secondNodes (i : Fin 5) : Node (polynomialReference P p q) :=
  transportPolynomialNode P p q
    (BassMComponents.polynomialNodes P p q (BassMOuterJoin.secondTargetWordIndex i))

private theorem first_original_nodes (i : Fin 5) :
    BassMComponents.polynomialNodes P p q (BassMOuterJoin.firstTargetWordIndex i) =
      postReferenceNode (BassMComponents.polynomialSource P p q)
        (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
        (firstBaseAnchor P p q) (CoefficientSquareFamilies.polynomialNodes P p i) :=
  CoefficientMovingSquareRows.first_row_nodes
    (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm i

private theorem second_original_nodes (i : Fin 5) :
    BassMComponents.polynomialNodes P p q (BassMOuterJoin.secondTargetWordIndex i) =
      preReferenceNode (BassMComponents.polynomialSource P p q)
        (normalizedMap (coefficientMap P p)) (secondBaseAnchor P p q)
        (CoefficientSquareFamilies.polynomialNodes P q i) :=
  CoefficientMovingSquareRows.second_row_nodes
    (coefficientMap P p) (coefficientMap P q)
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm i

/-- Every first full node is the original p-square node with its actual q-postcomposition. -/
theorem first_nodes (i : Fin 5) :
    firstNodes P p q i = postReferenceNode (polynomialReference P p q)
      (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
      (firstAnchor P p q) (CoefficientSquareFamilies.polynomialNodes P p i) := by
  unfold firstNodes
  rw [first_original_nodes]
  simp only [transportPolynomialNode, anchorNode, postReferenceNode, firstAnchor, Iso.trans_assoc]

/-- Every second full node is the original q-square node with its actual p-precomposition. -/
theorem second_nodes (i : Fin 5) :
    secondNodes P p q i = preReferenceNode (polynomialReference P p q)
      (normalizedMap (coefficientMap P p)) (secondAnchor P p q)
      (CoefficientSquareFamilies.polynomialNodes P q i) := by
  unfold secondNodes
  rw [second_original_nodes]
  simp only [transportPolynomialNode, anchorNode, preReferenceNode, secondAnchor, Iso.trans_assoc]

/-- The midpoint is the same complete polynomial node M13 before either chart attachment. -/
theorem first_target_second_source : firstNodes P p q 4 = secondNodes P p q 2 := rfl

/-- The first source is the exact terminal C1 polynomial node, including its reference. -/
theorem first_source_node : firstNodes P p q 2 = polynomialNodes P p q 2 := by
  change anchorNode (BassMOuterJoin.movingSideBaseIso P p q).symm
    (BassMComponents.polynomialNodes P p q
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex 2))) =
    precompNode (BassOverlap.projectionMap P (a := a)) (BassMOuterJoin.sideBinaryNodes P p q 2)
  have hn := congrArg (anchorNode (BassMOuterJoin.movingSideBaseIso P p q).symm)
    (BassMOuterJoin.rectangle_last_right_nodes
      (coefficientMap P p) (coefficientMap P q)
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
      (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm 2)
  exact hn.trans (anchor_pre_cancel (BassMComponents.polynomialSource P p q)
    (BassOverlap.projectionMap P (a := a)) (BassMOuterJoin.movingSideBaseIso P p q)
    (BassMOuterJoin.sideBinaryNodes P p q 2))

/-- The second target is the exact original coefficient-column target M11. -/
theorem second_target_coefficient_node :
    secondNodes P p q 4 = coefficientPolynomialNodes P p q 2 := rfl

/-- The second target retains the complete original q-pre-p polynomial null reference. -/
theorem second_target_node : secondNodes P p q 4 =
    CoefficientBassPositiveC0PolynomialEndpoints.targetNullNode P p q :=
  (second_target_coefficient_node P p q).trans
    (CoefficientBassPositiveC0PolynomialEndpoints.target_node P p q)

/-- The first family attaches to the complete original product target column. -/
theorem first_attach_nodes (i : Fin 5) :
    ordinaryAttachNode P p q (firstNodes P p q i) =
      BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b)
        (Quillen.SimplexGrid.index 4 4 (i, 4)) := by
  rw [firstNodes, attach_transport]
  exact BassMOuterJoin.plus_first_target_word_nodes P p q i

/-- The second family attaches to the complete original q polynomial row. -/
theorem second_attach_nodes (i : Fin 5) :
    ordinaryAttachNode P p q (secondNodes P p q i) =
      BassMOuterJoin.h1MiddleChartNodes P p q (underToLaurent R) (laurentPlus_projection P b)
        (polynomialWordIndex i) := by
  rw [secondNodes, attach_transport]
  exact BassMOuterJoin.plus_second_target_word_nodes P p q i

/-- The same second attachment is the full positive row in the fixed H1 middle family. -/
theorem second_attach_middle_nodes (i : Fin 5) :
    ordinaryAttachNode P p q (secondNodes P p q i) =
      BassH1References.middleNodes P p q
        (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)) := by
  rw [second_attach_nodes]
  exact (congrArg (preReferenceNode (laurentReference P p q)
    (BassH1Components.coefficientMapModel P p) (BassH1References.middleIso P p q))
    (BassH0Diagram.plus_nodes P q (polynomialWordIndex i))).symm

private theorem shifted_attach_node (N : Node (polynomialReference P p q)) :
    shiftedAttachNode P p q N =
      anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (ordinaryAttachNode P p q N) := by
  simp only [shiftedAttachNode, ordinaryAttachNode, attachPostcompNode, anchorNode,
    Iso.trans_assoc]

/-- The first shifted attachment retains the distinct common-unit-shifted product nodes. -/
theorem first_shifted_attach_nodes (i : Fin 5) :
    shiftedAttachNode P p q (firstNodes P p q i) =
      anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b)
          (Quillen.SimplexGrid.index 4 4 (i, 4))) := by
  rw [shifted_attach_node, first_attach_nodes]

/-- The second shifted attachment retains the distinct common-unit-shifted middle nodes. -/
theorem second_shifted_attach_nodes (i : Fin 5) :
    shiftedAttachNode P p q (secondNodes P p q i) =
      anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH1References.middleNodes P p q
          (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i))) := by
  rw [shifted_attach_node, second_attach_middle_nodes]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialNodes
