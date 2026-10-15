/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomPositiveColumn

/-! The original inverse source column, with its positive-to-inverse projection transport. -/
@[expose] public section

open Quillen.PerfectComplexes.BassReferenceMerge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
open BassReferenceMerge

/-- A genuine scheme equality transports the original binary normalization reference canonically. -/
theorem binary_anchor_change {X Y Z : Scheme.{u}}
    (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
    (f : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g')
    (e : F.functor = (BinaryNormalizationSimplex.sourceMap f g).functor)
    (e' : F.functor = (BinaryNormalizationSimplex.sourceMap f g').functor) :
    (eqToIso e ≪≫ BinaryNormalizationSimplex.total f g) ≪≫
      isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hg))
        (normalizedMap f).functor =
      eqToIso e' ≪≫ BinaryNormalizationSimplex.total f g' := by
  subst g'
  rw [eqToIso_refl, isoWhiskerRight_refl]
  exact Iso.trans_refl _

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual inverse projection total equals the fixed old common total. -/
theorem bottom_minus_reference_eq : (BassOverlap.commonReference P u v).functor =
    (NormalizedTripleSimplex.sourceMap (laurentComposite P u v)
      (laurentMinus P a) (polynomialProjection P a)).functor :=
  (bottom_reference_eq P u v).trans
    (congrArg (fun k ↦ (BinaryNormalizationSimplex.sourceMap (laurentComposite P u v) k).functor)
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm))

/-- The old positive-to-inverse source iso is exactly the canonical transported bottom anchor. -/
theorem bottom_minus_anchor_iso :
    BassBottomCommonFamily.referenceIso P u v ≪≫
      isoWhiskerRight (BassProjectionPath.sourceIso P a)
        (normalizedMap (laurentComposite P u v)).functor =
      eqToIso (bottom_minus_reference_eq P u v) ≪≫ BinaryNormalizationSimplex.total
        (laurentComposite P u v) (laurentMinus P a ≫ polynomialProjection P a) := by
  rw [bottom_anchor_iso]
  exact binary_anchor_change _ (laurentComposite P u v)
    ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm) _ _

/-- The two noninitial inverse binary nodes retain the original source reference transport. -/
theorem projection_minus_nodes (i : Fin 2) :
    BassProjectionPath.nodes P a (Fin.natAdd 3 i) =
      (⟨(binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).1,
        BassProjectionPath.sourceIso P a ≪≫
          (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2⟩ :
        BassProjectionPath.Node P a) := by
  fin_cases i <;> rfl

/-- Both original inverse bottom nodes agree with their canonically anchored binary column. -/
theorem bottom_minus_column (i : Fin 2) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.bottomFace.toOrderHom
      (Quillen.SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) =
      binaryColumnNode (BassOverlap.commonReference P u v) (laurentComposite P u v)
        (laurentMinus P a) (polynomialProjection P a) (bottom_minus_reference_eq P u v) i.succ := by
  rw [BassReferenceMerge.bottom_nodes]
  change BassBottomCommonFamily.nodes P u v
    (Fin.natAdd 36 (Quillen.SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_right]
  unfold BassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  rw [projection_minus_nodes P (a := a) i]
  have hf : ((binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).1 ≫
      BassLaurentBottomFace.vertices P u v 0).functor =
    (binaryColumnNode (BassOverlap.commonReference P u v) (laurentComposite P u v)
      (laurentMinus P a) (polynomialProjection P a)
      (bottom_minus_reference_eq P u v) i.succ).1.functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BassProjectionPath.sourceIso P a ≪≫
          (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2).prod
        (Iso.refl (normalizedMap (laurentComposite P u v)).functor)) =
      (eqToIso (bottom_minus_reference_eq P u v) ≪≫ BinaryNormalizationSimplex.total
        (laurentComposite P u v) (laurentMinus P a ≫ polynomialProjection P a)) ≪≫
          isoWhiskerRight (binaryNodes (laurentMinus P a) (polynomialProjection P a) i.succ).2
            (normalizedMap (laurentComposite P u v)).functor
  rw [composition_pair_refl, isoWhiskerRight_trans, ← Iso.trans_assoc, bottom_minus_anchor_iso]

/-- Both inverse source-edge nodes agree fully, including the distinct raw intermediate. -/
theorem negative_source_nodes (i : Fin 2) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i.succ)) =
      BassReferenceMerge.nodes P u v (BassReferenceMerge.bottomFace.toOrderHom
        (Quillen.SimplexGrid.index 4 2 (Fin.natAdd 3 i, 0))) := by
  rw [minus_source_column, bottom_minus_column]
  exact binaryColumnNode_congr _ _ _ _ _ (laurent_composite P u v) _ i.succ

/-- Full shared raw inverse node (H0 index 14, old merged index 39). -/
theorem shared_negative_raw_node : nodes P u v 14 = BassReferenceMerge.nodes P u v 39 :=
  negative_source_nodes P u v 0

/-- Full shared normalized inverse endpoint (H0 index 22, old merged index 42). -/
theorem shared_negative_target_node : nodes P u v 22 = BassReferenceMerge.nodes P u v 42 :=
  negative_source_nodes P u v 1

end Quillen.PerfectComplexes.BassH0Merge
