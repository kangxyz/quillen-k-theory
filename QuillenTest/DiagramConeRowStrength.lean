/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramConeRowStrengthHomotopy
public import Quillen.Topology.Prespectrum.RowRefinementParameterLooping

/-! The original target, two charts, and whole overlap retain every quotient and row coordinate. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.DiagramConeRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Quillen.LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (X : C)

/-- The target corner remains the original inclusion at every positive row value. -/
theorem target_succ (k : ℕ) (s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).right.right).point (k + 2))
      ((F.obj (Q.obj X).right.right).point (k + 2))) :
    Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
      ((mappingConeInclusion (StrictSquare.comparison
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)))).map
          (k + 1) γ)) s =
      (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).map
        (k + 2) (γ s) := rfl

/-- The upper chart preserves both its cone height and original row value. -/
theorem upper_succ (k : ℕ) (t s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).left.right).point (k + 2))
      ((F.obj (Q.obj X).left.right).point (k + 2))) :
    Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
      ((mappingConeHomotopy (StrictSquare.comparison
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)))).level
          (k + 1) (t, HomotopyPushout.left
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).left.hom)
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).hom.left) (k + 1) γ))) s =
      (mappingConeHomotopy (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).level
        (k + 2) (t, HomotopyPushout.left (F.map (Q.obj X).left.hom)
          (F.map (Q.obj X).hom.left) (k + 2) (γ s)) := rfl

/-- The lower chart preserves both its cone height and original row value. -/
theorem lower_succ (k : ℕ) (t s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).right.left).point (k + 2))
      ((F.obj (Q.obj X).right.left).point (k + 2))) :
    Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
      ((mappingConeHomotopy (StrictSquare.comparison
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)))).level
          (k + 1) (t, HomotopyPushout.right
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).left.hom)
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).hom.left) (k + 1) γ))) s =
      (mappingConeHomotopy (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).level
        (k + 2) (t, HomotopyPushout.right (F.map (Q.obj X).left.hom)
          (F.map (Q.obj X).hom.left) (k + 2) (γ s)) := rfl

/-- The entire overlap retains independent cone, overlap and row coordinates. -/
theorem overlap_succ (k : ℕ) (t b s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).left.left).point (k + 2))
      ((F.obj (Q.obj X).left.left).point (k + 2))) :
    Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
      ((mappingConeHomotopy (StrictSquare.comparison
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)))).level
          (k + 1) (t, HomotopyPushout.cylinder
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).left.hom)
            ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).hom.left)
              (k + 1) (b, γ)))) s =
      (mappingConeHomotopy (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).level
        (k + 2) (t, HomotopyPushout.cylinder (F.map (Q.obj X).left.hom)
          (F.map (Q.obj X).hom.left) (k + 2) (b, γ s)) := rfl

/-- The full zero-level overlap retains both row times and both original quotient heights. -/
theorem overlap_zero (t b r s : unitInterval)
    (γ : Path (Path.refl ((F.obj (Q.obj X).left.left).point 2))
      (Path.refl ((F.obj (Q.obj X).left.left).point 2))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((DiagramConeRowStrength.strength Q F q hp hn X).map 0
        ((mappingConeHomotopy (StrictSquare.comparison
          ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)))).level
            0 (t, HomotopyPushout.cylinder
              ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).left.hom)
              ((DiagramRowRefinement.diagram F q hp hn).map (Q.obj X).hom.left)
                0 (b, γ)))) r) s =
      (mappingConeHomotopy (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).level
        2 (t, HomotopyPushout.cylinder (F.map (Q.obj X).left.hom)
          (F.map (Q.obj X).hom.left) 2 (b, γ r s)) := rfl

end QuillenTest.DiagramConeRowStrength
