/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTransformationComposition

/-!
# Composition of original geometric transformation squares

Every natural transformation between actual scheme endofunctors has a whole moving
composition square. The existing geometric rectangle and both functor composition transports
are retained; no coefficient-model identification or higher filler is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTransformations
variable {M N : Scheme.{u} ⥤ Scheme.{u}} (α : N ⟶ M)
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Functor-applied composition retains the original split track and actual map composition. -/
def composition (M : Scheme.{u} ⥤ Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (M.map (f ≫ g)))
      (boundedFlatPerfectPrespectrumMap (M.map g) ≫
        boundedFlatPerfectPrespectrumMap (M.map f)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (M.map f) (M.map g)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (M.map_comp f g)).symm rfl

/-- The actual naturality square of the geometric transformation. -/
def square {U V : Scheme.{u}} (k : U ⟶ V) :=
  boundedFlatPerfectPrespectrumSquareHomotopy (N.map k) (α.app V) (α.app U)
    (M.map k) (α.naturality k)

/-- The maintained whole geometric rectangle on the actual three transformation components. -/
def rectangle :=
  DoubleSquareTrack.originalComparison (M.map g) (M.map f) (N.map g) (N.map f)
    (α.app Z) (α.app Y) (α.app X)
    (α.naturality g).symm (α.naturality f).symm

/-- The two successive original transformation squares with their unchanged associations. -/
def compositeSquare :=
  ((square α g).postcomp
    (boundedFlatPerfectPrespectrumMap (N.map f))).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (M.map g))
      (square α f)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- The original source composition followed by the actual target transformation. -/
def sourceTrack :=
  (composition f g M).postcomp (boundedFlatPerfectPrespectrumMap (α.app X))

/-- The actual target composition under the unchanged source transformation. -/
def targetTrack :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (α.app Z))
    (composition f g N)).cast rfl (Category.assoc _ _ _).symm

/-- Every initial rectangle value is the two original successive transformation squares. -/
theorem rectangle_source_level (n : ℕ) :
    (compositeSquare α f g).level n = (((rectangle α f g).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold DoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  unfold compositeSquare
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (N.map g) (α.app Z) (α.app Y) (M.map g)
      (α.naturality g) n).symm
  · change (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (M.map g))
      (square α f)).level n =
        (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (M.map g))
          (boundedFlatPerfectPrespectrumSquareHomotopy
            (α.app X) (M.map f) (N.map f) (α.app Y)
            (α.naturality f).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (N.map f) (α.app Y) (α.app X) (M.map f)
      (α.naturality f) n).symm

/-- The full terminal rectangle retains the direct square and both composition tracks. -/
theorem rectangle_target_level (n : ℕ) :
    (((targetTrack α f g).symm.trans (square α (f ≫ g))).trans
      (sourceTrack α f g)).level n = (((rectangle α f g).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold DoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (boundedFlatGeometricSquareReverse_level
        (N.map (f ≫ g)) (α.app Z) (α.app X) (M.map (f ≫ g))
        (α.naturality (f ≫ g)) n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact boundedFlatGeometricSquare_level_congr _ _ rfl
        (M.map_comp f g) (N.map_comp f g) rfl n
  · rfl

/-- The original geometric rectangle gives the complete transformation composition comparison. -/
def comparison :
    (compositeSquare α f g).RelHomotopy
      (((targetTrack α f g).symm.trans (square α (f ≫ g))).trans
        (sourceTrack α f g)) :=
  Homotopy.RelHomotopy.ofLevels (rectangle α f g).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using rectangle_source_level α f g n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using rectangle_target_level α f g n)

/-- Rotate the actual rectangle to the direct-to-composite moving-square boundary. -/
def boundary :
    (square α (f ≫ g)).RelHomotopy
      (((targetTrack α f g).trans (compositeSquare α f g)).trans (sourceTrack α f g).symm) := by
  let B := targetTrack α f g
  let A := sourceTrack α f g
  let H := square α (f ≫ g)
  let K := compositeSquare α f g
  have J := comparison α f g
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((Homotopy.RelHomotopy.refl B).hcomp J).trans
      (((Homotopy.RelHomotopy.transAssoc B (B.symm.trans H) A).symm).trans
        ((((Homotopy.RelHomotopy.transAssoc B B.symm H).symm).hcomp
          (Homotopy.RelHomotopy.refl A)).trans
          ((((Homotopy.RelHomotopy.reflTransSymm B).symm.hcomp
            (Homotopy.RelHomotopy.refl H)).hcomp (Homotopy.RelHomotopy.refl A)).trans
            ((Homotopy.RelHomotopy.reflTrans H).hcomp (Homotopy.RelHomotopy.refl A)))))
  exact (Homotopy.RelHomotopy.transRefl H).symm.trans
    (((Homotopy.RelHomotopy.refl H).hcomp (Homotopy.RelHomotopy.reflTransSymm A)).trans
      (((Homotopy.RelHomotopy.transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (Homotopy.RelHomotopy.refl A.symm))))

/-- The actual whole transformation composition square, with both original geometric sides. -/
def movingSquare := (boundary α f g).toSquare

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTransformations
