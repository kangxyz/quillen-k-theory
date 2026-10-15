/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceMiddleCenter

/-! Both full binary rows on the original M-source/H0-target middle path. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original first product row retains every complete projection-path reference. -/
theorem middle_source_row (j : Fin 5) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (0, j)) =
    preReferenceNode (BassOverlap.commonReference P u v) (coefficientSource P u v)
      (middleIso P u v) (BassProjectionPath.nodes P c j) := by
  have hn := product_row_nodes (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (fun i ↦ (coefficientNodes P u v i).1)
    (fun i ↦ (coefficientNodes P u v i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) (middleIso P u v) 0 j
  change _ = preReferenceNode (BassOverlap.commonReference P u v) (coefficientSource P u v)
    (middleIso P u v ≪≫ isoWhiskerRight (Iso.refl (coefficientSource P u v).functor)
      (BassProjectionPath.source P c).functor) (BassProjectionPath.nodes P c j) at hn
  rw [isoWhiskerRight_refl] at hn
  exact hn.trans (congrArg (fun ρ ↦
    preReferenceNode (BassOverlap.commonReference P u v) (coefficientSource P u v)
      ρ (BassProjectionPath.nodes P c j)) (Iso.trans_refl (middleIso P u v)))

/-- The inverse projection triangle retains the actual transported source as a full node. -/
theorem projection_minus_all (i : Fin 3) :
    BassProjectionPath.nodes P c (BassProjectionPath.minusFace.toOrderHom i) =
    anchorNode (BassProjectionPath.sourceIso P c)
      (binaryNodes (laurentMinus P c) (polynomialProjection P c) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (BassProjectionPath.source_eq P c)
    simp [BassProjectionPath.sourceIso, binaryNodes]
  · rfl
  · rfl

/-- The original positive product source row uses its literal binary projection family. -/
theorem middle_source_plus_row (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (0, Fin.castAdd 2 i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (coefficientSource P u v)
      (middleIso P u v) (binaryNodes (laurentPlus P c) (polynomialProjection P c) i) := by
  rw [middle_source_row, projection_plus_nodes P (a := c)]

/-- The actual inverse product source anchor includes the original positive-to-inverse transport. -/
def middleSourceMinusIso := middleIso P u v ≪≫
  isoWhiskerLeft (coefficientSource P u v).functor (BassProjectionPath.sourceIso P c)

/-- The original inverse source row retains every actual node after that source transport. -/
theorem middle_source_minus_row (i : Fin 3) :
    middleNodes P u v
      (Quillen.SimplexGrid.index 2 4 (0, BassProjectionPath.minusFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (coefficientSource P u v)
      (middleSourceMinusIso P u v)
      (binaryNodes (laurentMinus P c) (polynomialProjection P c) i) := by
  rw [middle_source_row, projection_minus_all]
  exact pre_anchor_node (BassOverlap.commonReference P u v) (coefficientSource P u v)
    (middleIso P u v) (BassProjectionPath.sourceIso P c)
    (binaryNodes (laurentMinus P c) (polynomialProjection P c) i)

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- H0's actual complete target row keeps its unchanged common-reference transport. -/
def oldTargetRowIso := eqToIso (reference_eq P u v) ≪≫
  BassH1H0Boundary.targetRowReference P (u ≫ v) α ha

/-- H0's full positive target row, in the same original common-reference type. -/
theorem old_target_plus_row (i : Fin 3) :
    BassH0Merge.nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    preReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (u ≫ v)))
      (oldTargetRowIso P u v (underToLaurent R) (laurentPlus_projection P a))
      (binaryNodes (laurentPlus P c) (polynomialProjection P c) i) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (BassH1H0Boundary.plus_target P (u ≫ v) i)
  exact hn.trans (anchor_pre_node (normalizedMap (coefficientMap P (u ≫ v)))
    (eqToIso (reference_eq P u v))
    (BassH1H0Boundary.targetRowReference P (u ≫ v) (underToLaurent R)
      (laurentPlus_projection P a)) (binaryNodes (laurentPlus P c) (polynomialProjection P c) i))

/-- H0's full inverse target row retains its separate original projection family. -/
theorem old_target_minus_row (i : Fin 3) :
    BassH0Merge.nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    preReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (u ≫ v)))
      (oldTargetRowIso P u v (underToLaurentInvert R) (laurentMinus_projection P a))
      (binaryNodes (laurentMinus P c) (polynomialProjection P c) i) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (BassH1H0Boundary.minus_target P (u ≫ v) i)
  exact hn.trans (anchor_pre_node (normalizedMap (coefficientMap P (u ≫ v)))
    (eqToIso (reference_eq P u v))
    (BassH1H0Boundary.targetRowReference P (u ≫ v) (underToLaurentInvert R)
      (laurentMinus_projection P a)) (binaryNodes (laurentMinus P c) (polynomialProjection P c) i))

/-- The two source coefficient model maps agree by original coefficient composition. -/
theorem source_coefficient_map : coefficientSource P u v =
    normalizedMap (coefficientMap P (u ≫ v)) :=
  congrArg normalizedMap (coefficientMap_comp P u v).symm

/-- The entire positive M-source/H0-target binary row agrees as full dependent reference nodes. -/
theorem source_middle_plus_nodes (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (0, Fin.castAdd 2 i)) =
    BassH0Merge.nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) :=
  pre_families_match_maps (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (normalizedMap (coefficientMap P (u ≫ v)))
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P c) (polynomialProjection P c))
    (source_coefficient_map P u v) (binaryNodes (laurentPlus P c) (polynomialProjection P c))
    (middle_source_plus_row P u v) (old_target_plus_row P u v) 0 (source_middle_center P u v) i

/-- The inverse row retains its full reference transport and every original normalization node. -/
theorem source_middle_minus_nodes (i : Fin 3) :
    middleNodes P u v
      (Quillen.SimplexGrid.index 2 4 (0, BassProjectionPath.minusFace.toOrderHom i)) =
    BassH0Merge.nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) :=
  pre_families_match_maps (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (normalizedMap (coefficientMap P (u ≫ v)))
    (BinaryNormalizationSimplex.sourceMap (laurentMinus P c) (polynomialProjection P c))
    (source_coefficient_map P u v) (binaryNodes (laurentMinus P c) (polynomialProjection P c))
    (middle_source_minus_row P u v) (old_target_minus_row P u v) 0 (source_middle_center P u v) i

/-- The complete five-node original middle source path is shared with H0's original target. -/
theorem source_middle_path_nodes (i : Fin 5) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (0, i)) =
    BassH0Merge.nodes P u v (BassH1Join.firstMiddleFace.toOrderHom i) := by
  fin_cases i
  · exact source_middle_center P u v
  · exact source_middle_plus_nodes P u v 1
  · exact source_middle_plus_nodes P u v 2
  · exact source_middle_minus_nodes P u v 1
  · exact source_middle_minus_nodes P u v 2

end Quillen.PerfectComplexes.BassMOuterJoin
