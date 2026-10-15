/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelComposition

/-!
# Unchanged common-universe coefficient tracks

The smaller coefficient construction is the original Model isomorphism, hence retains every
level of the original homotopy, including its loop level and independent structure coordinate.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.BoundedFlatModelCoefficient

open Quillen

/-- The lifted comparison is exactly the unchanged original coefficient Model iso. -/
theorem original_iso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionLiftedCoefficientIso f =
      boundedFlatAffineSectionEvaluationCoefficientIso f :=
  boundedFlatAffineSectionLiftedCoefficientIso_eq f

/-- The original transformation homotopy treats its iso and weak proof together. -/
def isoTrack {V W : Model.{u}} {F G : V ⟶ W} (i : F.functor ≅ G.functor) :=
  prespectrumTransformationHomotopy i.hom
    (fun A => W.waldhausen.weq_iso _ (by change IsIso (i.hom.app A); infer_instance))

/-- The original Model transformation construction applied to the smaller lifted iso. -/
def liftedTrack {R S : CommRingCat.{u}} (f : R ⟶ S) :=
  isoTrack
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec S)))
    (F := boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionEvaluationModelMap S)
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f)
    (boundedFlatAffineSectionLiftedCoefficientIso f)

/-- Every complete original coefficient track is preserved under the generic universe lift. -/
theorem original_whole_level {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    (liftedTrack f).level n =
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n := by
  have h := congrArg (fun i => (isoTrack
    (V := boundedFlatAffineSectionModel R)
    (W := modelOf (boundedFlatPerfectWaldhausen (Spec S)))
    (F := boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionEvaluationModelMap S)
    (G := boundedFlatAffineSectionEvaluationModelMap R ≫
      boundedFlatAffineOriginalCoefficientModelMap f) i).level n)
    (boundedFlatAffineSectionLiftedCoefficientIso_eq f)
  exact h

/-- At degree zero the original loop variable is independent of the coefficient-track time. -/
theorem original_loop_value {R S : CommRingCat.{u}} (f : R ⟶ S)
    (r q : unitInterval)
    (γ : Path (stagePoint 0 (boundedFlatAffineSectionModel R))
      (stagePoint 0 (boundedFlatAffineSectionModel R))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S)))) from
        (liftedTrack f).level 0 (r, γ)) q =
      (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S))))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (Spec S)))) from
          (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level 0 (r, γ)) q := by
  rw [original_whole_level]
  rfl

/-- Structure time remains independent of the complete unchanged coefficient-track time. -/
theorem original_structure_time {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (r t : unitInterval) (x : (prespectrum (boundedFlatAffineSectionModel R)).space n) :
    (liftedTrack f).level (n + 1)
        (r, (prespectrum (boundedFlatAffineSectionModel R)).structureMap n x t) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen (Spec S)))).structureMap n
        ((liftedTrack f).level n (r, x)) t :=
  (liftedTrack f).comm n r x t

end QuillenTest.BoundedFlatModelCoefficient
