/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1InternalScalarJoins

/-! The original full central node on the external H1/bottom boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The actual positive projection equation in the original first component's source. -/
theorem bottomSourceGeom :
    coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a =
      coefficientMap P ((laurentUnderFunctor R).map u) ≫
        (laurentPlus P a ≫ polynomialProjection P a) :=
  congrArg (fun h ↦ coefficientMap P ((laurentUnderFunctor R).map u) ≫ h)
    (laurentPlus_projection P a).symm

def firstBottomCenter : BassOverlap.Node P u v :=
  postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a),
      eqToIso (BassH1H0Boundary.sourceAnchor P u (underToLaurent R)
        (laurentPlus_projection P a)) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)⟩ : BassH0Diagram.Node P u)

def bottomTargetCenter : BassOverlap.Node P u v :=
  BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassProjectionPath.source P a) (BassBottomCommonFamily.referenceIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)),
      BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u))⟩ :
      Σ G, (BassLaurentBottomFace.source P u v).functor ≅ G.functor)

theorem first_bottom_center_original : BassH1References.firstNodes P u v 2 =
    firstBottomCenter P u v := rfl

/-- The bottom's actual final column retains the original Laurent normalization reference. -/
theorem bottom_target_center_original : BassBottomCommonFamily.bottomNodes P u v 2 =
    bottomTargetCenter P u v := by
  change BassBottomCommonFamily.bottomNodes P u v (Quillen.SimplexGrid.index 4 2 (0, 2)) = _
  unfold BassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  have hf : ((BassProjectionPath.nodes P a 0).1 ≫ BassLaurentBottomFace.vertices P u v 2).functor =
      (bottomTargetCenter P u v).1.functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (BassProjectionPath.source P a).functor).prod
        (BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P ((laurentUnderFunctor R).map u)))) = _
  have hi := composition_pair_iso (Iso.refl (BassProjectionPath.source P a).functor)
    (BinaryNormalizationSimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)))
  simp only [isoWhiskerRight_refl, Iso.refl_trans] at hi
  exact congrArg (fun ν ↦ BassBottomCommonFamily.referenceIso P u v ≪≫ ν) hi

theorem bottom_center_functor : (firstBottomCenter P u v).1.functor =
    (bottomTargetCenter P u v).1.functor := rfl

/-- The source/bottom common node keeps the actual projection and Laurent composition isos. -/
theorem bottom_center_reference : (firstBottomCenter P u v).2 =
    (bottomTargetCenter P u v).2 := by
  have he : eqToIso (BassH1H0Boundary.sourceAnchor P u (underToLaurent R)
      (laurentPlus_projection P a)) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (bottomSourceGeom P u)) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (BassH1H0Boundary.sourceAnchor P u (underToLaurent R)
        (laurentPlus_projection P a)) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)) (BassH1Components.laurentMap P v).functor =
    BassBottomCommonFamily.referenceIso P u v ≪≫
      isoWhiskerLeft (BassProjectionPath.source P a).functor
        (BinaryNormalizationSimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P ((laurentUnderFunctor R).map u)))
  rw [he]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (first_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (bottomSourceGeom P u)) ≪≫
        boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map u))
          (laurentPlus P a ≫ polynomialProjection P a)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫
          coefficientMap P ((laurentUnderFunctor R).map u))
        (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback
      (laurentPlus P a ≫ polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (laurentPlus P a ≫ polynomialProjection P a)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫
        coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (bottomSourceGeom P u) (BassBottomCommonFamily.bottom_total P u v).symm
      (first_total P u v).symm).symm

/-- Full original first/bottom central node, before the previously fixed old62 relabeling. -/
theorem first_bottom_center : BassH1References.firstNodes P u v 2 =
    BassBottomCommonFamily.bottomNodes P u v 2 := by
  rw [first_bottom_center_original, bottom_target_center_original]
  apply Sigma.ext (Model.Hom.ext (bottom_center_functor P u v))
  exact heq_of_eq (bottom_center_reference P u v)

/-- The same full central node in the unchanged original44 chart/bottom family. -/
theorem first_old_bottom_center : BassH1References.firstNodes P u v 2 =
    BassReferenceMerge.nodes P u v 17 := first_bottom_center P u v

/-- The exact full central node in the fixed H0/chart/bottom62 family. -/
theorem first_old62_bottom_center : BassH1References.firstNodes P u v 2 =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex 17) :=
  (first_old_bottom_center P u v).trans (BassH0Merged.old_nodes P u v 17).symm

end Quillen.PerfectComplexes.BassH1Join
