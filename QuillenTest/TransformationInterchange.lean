/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.TransformationInterchange
public import Quillen.Topology.Prespectrum.StrictSquareSeedHomotopy

/-!
# Consumers of the original two-time scalar and weak-transformation cylinders

These retain both actual simplicial times, the third degree-zero loop coordinate, and the
independent prespectrum structure parameter. Identity actions give a concrete specialization
without supplied scalar equations. The original source null cylinder and source-seed values
use exactly the already constructed moving strict-square map.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace QuillenTest.TransformationInterchange

open Quillen
variable {V W : Model.{u}} {F G : V ⟶ W} (η : F.functor ⟶ G.functor)
    (α : (𝟙 V : V ⟶ V).functor ⟶ (𝟙 V : V ⟶ V).functor)
    (β : (𝟙 W : W ⟶ W).functor ⟶ (𝟙 W : W ⟶ W).functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hα : ∀ X, V.waldhausen.weq (α.app X))
    (hβ : ∀ X, W.waldhausen.weq (β.app X))
    (hF : ∀ X, F.functor.map (α.app X) = β.app (F.functor.obj X))
    (hG : ∀ X, G.functor.map (α.app X) = β.app (G.functor.obj X))

include hF hG in
/-- Both original simplicial parameters survive at every iterated S stage. -/
theorem original_simplicial_two_times (r : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    stageTransformationFunction r η hη n (stageTransformationFunction r α hα n A τ) θ =
      stageTransformationFunction r β hβ n (stageTransformationFunction r η hη n A θ) τ :=
  stageTransformationFunction_identityAction_interchange r η α β hη hα hβ hF hG n A τ θ

include hF hG in
/-- The reversed null, scalar and actual degree-zero loop times remain independent. -/
theorem original_zero_level_three_times (s t q : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap ((prespectrumTransformationHomotopy η hη).symm.level 0
        (s, (prespectrumTransformationHomotopy α hα).level 0 (t, γ))) q =
      Path.toContinuousMap ((prespectrumTransformationHomotopy β hβ).level 0
        (t, (prespectrumTransformationHomotopy η hη).symm.level 0 (s, γ))) q :=
  congrArg (fun p => Path.toContinuousMap p q)
    (prespectrumTransformationHomotopy_symm_identityAction_interchange
      η α β hη hα hβ hF hG 0 s t γ)

/-- Original structure time is independent of both transformation-cylinder times. -/
theorem original_structure_time (n : ℕ) (s t q : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy η hη).level (n + 1)
        (s, (prespectrumTransformationHomotopy α hα).level (n + 1)
          (t, (prespectrum V).structureMap n x q)) =
      (prespectrum W).structureMap n
        ((prespectrumTransformationHomotopy η hη).level n
          (s, (prespectrumTransformationHomotopy α hα).level n (t, x))) q := by
  rw [(prespectrumTransformationHomotopy α hα).comm,
    (prespectrumTransformationHomotopy η hη).comm]

/-- Genuine identity transformations discharge both endpoint scalar equations. -/
theorem original_identity_actions (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy η hη).level n
        (s, (prespectrumTransformationHomotopy (F := 𝟙 V) (G := 𝟙 V) (𝟙 (𝟭 V))
          (fun X => V.waldhausen.weq.id_mem X)).level n (t, x)) =
      (prespectrumTransformationHomotopy (F := 𝟙 W) (G := 𝟙 W) (𝟙 (𝟭 W))
        (fun X => W.waldhausen.weq.id_mem X)).level n
        (t, (prespectrumTransformationHomotopy η hη).level n (s, x)) :=
  prespectrumTransformationHomotopy_identityAction_interchange η (𝟙 (𝟭 V)) (𝟙 (𝟭 W))
    hη (fun X => V.waldhausen.weq.id_mem X) (fun X => W.waldhausen.weq.id_mem X)
    F.functor.map_id G.functor.map_id n s t x

/-- A moving original square preserves the entire source-leg null cylinder. -/
theorem original_source_null_square
    {S T : Arrow (Arrow LoopPrespectrum.{u})} {a b : S ⟶ T}
    (H : StrictSquare.MapHomotopy a b) (n : ℕ) (r s : unitInterval)
    (x : S.left.left.space n) :
    H.cone.level n (r, (StrictSquare.sourceNullHomotopy S).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy T).level n (s, H.source.level n (r, x)) :=
  H.sourceNull_apply n r s x

/-- Each original seed loop commutes at the same homotopy time after the scalar square is proved. -/
theorem original_source_seed_loop
    {S T : Arrow (Arrow LoopPrespectrum.{u})} {a b : S ⟶ T}
    (H : StrictSquare.MapHomotopy a b)
    (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
    (V : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
    (hU : ∀ n r s x, H.target.level n (r, U.level n (s, x)) =
      V.level n (s, H.source.level n (r, x)))
    (r t : unitInterval) (x : S.left.left.space 0) :
    Path.toContinuousMap
        (H.looped.level 0 (r,
          ((U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
            (StrictSquare.sourceNullHomotopy S)).map 0 x)) t =
      Path.toContinuousMap
        (((V.postcomp (mappingConeInclusion (StrictSquare.comparison T))).nullLoopMap
          (StrictSquare.sourceNullHomotopy T)).map 0 (H.source.level 0 (r, x))) t :=
  H.sourceSeed_apply U V hU 0 r t x

end QuillenTest.TransformationInterchange
