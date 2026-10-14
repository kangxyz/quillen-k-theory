/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H0OuterReferenceNodes

/-! Actual full central reference equality at the first/middle H1 cell boundary. -/
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
open BassReferenceMerge BassH1References BassH1H0Boundary

/-- Postcomposition/reanchoring of a full original reference node. -/
def postReferenceNode {V W T : Model.{u}} (F : V ⟶ T) (J : W ⟶ T) {H : V ⟶ W}
    (ρ : F.functor ≅ (H ≫ J).functor) (N : Σ G : V ⟶ W, H.functor ≅ G.functor) :
    Σ G : V ⟶ T, F.functor ≅ G.functor :=
  ⟨N.1 ≫ J, ρ ≪≫ isoWhiskerRight N.2 J.functor⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

def firstCenter : BassOverlap.Node P u v :=
  postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap (laurentProjection P b) (coefficientMap P u),
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback (laurent_naturality P u))) ≪≫
        BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P u)⟩ :
      BassH0Diagram.Node P u)

def middleCenter : BassOverlap.Node P u v :=
  BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b),
      BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)⟩ :
      BassH0Diagram.Node P v)

/-- This is the original first-component node, with only its proved geometric normal form used. -/
theorem first_center_original : BassH1References.firstNodes P u v 26 = firstCenter P u v :=
  congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v)) (target_normal P u)

/-- This is the original middle-component node, including its exact source normalization. -/
theorem middle_center_original : BassH1References.middleNodes P u v 2 = middleCenter P u v :=
  congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v)) (source_normal P v)

theorem center_functor : (firstCenter P u v).1.functor = (middleCenter P u v).1.functor := rfl

/-- The actual two normalization routes agree by three-factor pullback coherence. -/
theorem center_reference : (firstCenter P u v).2 = (middleCenter P u v).2 := by
  have he : eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
      (congrArg boundedFlatNormalizedPullback (laurent_naturality P u))) ≪≫
        BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P u) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (laurent_naturality P u)) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurentProjection P b) (coefficientMap P u)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback (laurent_naturality P u))) ≪≫
        BinaryNormalizationSimplex.total (laurentProjection P b) (coefficientMap P u))
      (BassH1Components.laurentMap P v).functor =
    middleIso P u v ≪≫ isoWhiskerLeft (BassH1Components.coefficientMapModel P u).functor
      (BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b))
  rw [he]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (first_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (laurent_naturality P u)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentProjection P b) (coefficientMap P u)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (middle_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
        (coefficientMap P u)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback (coefficientMap P u) ⋙ AsSmall.up)
      (smallIso (boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b)
      (coefficientMap P u)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (laurent_naturality P u) (middle_total P u v).symm (first_total P u v).symm).symm

/-- A full dependent H1 boundary node is shared, not merely its endpoint functor. -/
theorem first_middle_center : BassH1References.firstNodes P u v 26 =
    BassH1References.middleNodes P u v 2 := by
  rw [first_center_original, middle_center_original]
  apply Sigma.ext (Model.Hom.ext (center_functor P u v))
  exact heq_of_eq (center_reference P u v)

end Quillen.PerfectComplexes.BassH1Join
