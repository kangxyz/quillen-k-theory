/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0CommonReference

/-! The first actual full dependent node shared by H0 and the original bottom family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
open BassReferenceMerge

/-- The canonical anchored normalized target of an actual binary factorization. -/
def binaryTargetNode {X Y Z : Scheme.{u}}
    (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : F.functor = (BinaryNormalizationSimplex.sourceMap f g).functor) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X),
      F.functor ≅ G.functor :=
  ⟨BinaryNormalizationSimplex.targetMap f g, eqToIso e ≪≫ BinaryNormalizationSimplex.total f g⟩

/-- Actual equality of the two scheme factors retains the entire anchored target node. -/
theorem binaryTargetNode_congr {X Y Z : Scheme.{u}}
    (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ modelOf (boundedFlatPerfectWaldhausen X))
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (e : F.functor = (BinaryNormalizationSimplex.sourceMap f g).functor)
    (e' : F.functor = (BinaryNormalizationSimplex.sourceMap f' g').functor) :
    binaryTargetNode F f g e = binaryTargetNode F f' g' e' := by
  subst f'
  subst g'
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- H0's central source-path node is the actual normalized Laurent/projection factorization. -/
theorem source_node_canonical : nodes P u v 2 =
    binaryTargetNode (BassOverlap.commonReference P u v)
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a)
      (reference_eq P u v) := by
  have h := ProjectionReference.source_normal_node
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P c) (laurentPlus P c)
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
    (coefficientTransformation_naturality P (underToLaurent R) (u ≫ v))
    (laurentProjection P a) (laurentProjection P c)
    (laurentPlus_projection P a) (laurentPlus_projection P c)
  exact congrArg (fun N : ProjectionReference.Node
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a) ↦
    (⟨N.1, eqToIso (reference_eq P u v) ≪≫ N.2⟩ : BassOverlap.Node P u v)) h

/-- The original bottom total equality at its exact two-factor model functor. -/
theorem bottom_reference_eq : (BassOverlap.commonReference P u v).functor =
    (BinaryNormalizationSimplex.sourceMap (laurentComposite P u v)
      (laurentPlus P a ≫ polynomialProjection P a)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (BassBottomCommonFamily.bottom_total P u v).symm)

/-- The original bottom source uses its actual projection and Laurent binary reference. -/
theorem bottom_source_canonical : BassReferenceMerge.nodes P u v 15 =
    binaryTargetNode (BassOverlap.commonReference P u v)
      (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a)
      (bottom_reference_eq P u v) := by
  have hf : (BassReferenceMerge.nodes P u v 15).1.functor =
      (BinaryNormalizationSimplex.targetMap (laurentComposite P u v)
        (laurentPlus P a ≫ polynomialProjection P a)).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (BassProjectionPath.source P a).functor).prod
        (Iso.refl (BassLaurentBottomFace.source P u v).functor)) =
      eqToIso (bottom_reference_eq P u v) ≪≫ BinaryNormalizationSimplex.total
        (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a)
  rw [composition_pair_iso, isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_trans]
  refine (Iso.trans_refl (BassBottomCommonFamily.referenceIso P u v)).trans ?_
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
        (laurentPlus P a ≫ polynomialProjection P a)) = _
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- Full shared node (H0 index 2, old merged index 15), including both reference transports. -/
theorem shared_source_node : nodes P u v 2 = BassReferenceMerge.nodes P u v 15 := by
  rw [source_node_canonical, bottom_source_canonical]
  exact binaryTargetNode_congr _ (laurent_composite P u v) (laurentPlus_projection P a).symm _ _

end Quillen.PerfectComplexes.BassH0Merge
