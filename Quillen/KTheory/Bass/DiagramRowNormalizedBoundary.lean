/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowSeed
public import Quillen.Topology.Prespectrum.RowNormalization
public import Quillen.Topology.Prespectrum.RowNormalizedOperationNaturality

/-!
# Normalized independent cells followed by the original Bass boundary

The forward operation is defined by inverse-prefix normalization of an independent
last-corner cell, followed by the actual row map of the Laurent cone inclusion.
A whole spectrum homotopy compares it with the seed using the unchanged original
source null. No equality with a scalar action is needed for this construction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.DiagramRowSeed
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


variable (X : C)
  (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
    (diagonal Q F X ≫ cornerComparison Q F q hp hs X))

/-- Normalize the independent cell before applying the original refined boundary inclusion. -/
def normalizedBoundary :
    F.obj (Q.obj X).left.left ⟶ parameterLooping (carrier Q F q hp hn X) :=
  RowRefinement.normalizedOperation (q (Q.obj X).right.right)
    (hp (Q.obj X).right.right) (diagonal Q F X ≫ cornerComparison Q F q hp hs X) K ≫
      parameterLoopingMap (inclusion Q F q hp hn X)

/-- The original null, with only its source witness changed to the inclusion composite. -/
def includedNull :
    Homotopy ((diagonal Q F X ≫ cornerComparison Q F q hp hs X) ≫
      inclusion Q F q hp hn X) (zeroHom _ (carrier Q F q hp hn X)) :=
  (RefinedNullSeed.null (diagonal Q F X)
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (comparison Q F q hp hn hs X)
    (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X)))).cast
      (by simp only [Category.assoc, comparison_inclusion]) rfl

/-- Normalization commutes with the actual Laurent inclusion on the entire spectrum. -/
theorem normalizedBoundary_eq :
    normalizedBoundary Q F q hp hn hs X K =
      RowRefinement.normalizedOperation (DiagramRowInterchange.cone Q F q hp hn X)
        (DiagramRowInterchange.cone_point Q F q hp hn X)
        ((diagonal Q F X ≫ cornerComparison Q F q hp hs X) ≫ inclusion Q F q hp hn X)
        (K.postcomp (inclusion Q F q hp hn X)) := by
  exact RowRefinement.normalizedOperation_postcomp
    (q (Q.obj X).right.right) (DiagramRowInterchange.cone Q F q hp hn X)
    (hp (Q.obj X).right.right) (DiagramRowInterchange.cone_point Q F q hp hn X)
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (fun _ _ => rfl) _ K

/-- The normalized cell/boundary composite retains the specified original null at every level. -/
def normalizedBoundaryHomotopy :
    Homotopy (normalizedBoundary Q F q hp hn hs X K) (seed Q F q hp hn hs X K) := by
  have h := RowRefinement.normalizationHomotopy
    (DiagramRowInterchange.cone Q F q hp hn X)
    (DiagramRowInterchange.cone_point Q F q hp hn X)
    ((diagonal Q F X ≫ cornerComparison Q F q hp hs X) ≫ inclusion Q F q hp hn X)
    (K.postcomp (inclusion Q F q hp hn X)) (includedNull Q F q hp hn hs X)
  apply h.cast (normalizedBoundary_eq Q F q hp hn hs X K).symm
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

end Quillen.KTheory.Bass.DiagramRowSeed
