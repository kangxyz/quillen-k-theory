/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowInterchange
public import Quillen.Topology.Prespectrum.RowRefinementCone
public import Quillen.Topology.Prespectrum.RefinedNullSeed

/-!
# Independent row seeds on the original four-corner diagram

The original last-corner inclusion acts on the computed row refinement. An
independent cell then gives a seed using the image of the complete original
source null. A whole-cell equality supplies the original seed comparison.
-/
@[expose] public section
noncomputable section
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

/-- The original unlooped cone's actual computed row carrier. -/
abbrev carrier (X : C) := RowRefinement.spectrum ((ConeTrack.diagram Q F).obj X)
  (DiagramRowInterchange.cone Q F q hp hn X) (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- Its actual comparison from the original cone. -/
def comparison (X : C) : (ConeTrack.diagram Q F).obj X ⟶ carrier Q F q hp hn X :=
  RowRefinement.comparison _ _ _ (DiagramRowInterchange.cone_structure Q F q hp hn hs X)

/-- The last corner's genuine row comparison. -/
def cornerComparison (X : C) :=
  RowRefinement.comparison (F.obj (Q.obj X).right.right)
    (q (Q.obj X).right.right) (hp (Q.obj X).right.right) (hs (Q.obj X).right.right)

/-- The original last-corner inclusion acts on the actual row, at every coordinate. -/
def inclusion (X : C) :
    RowRefinement.spectrum (F.obj (Q.obj X).right.right)
      (q (Q.obj X).right.right) (hp (Q.obj X).right.right) ⟶ carrier Q F q hp hn X :=
  RowRefinement.map _ _ _ _
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (fun _ _ => rfl)

/-- The last-corner inclusion square uses the original cone comparison. -/
theorem comparison_inclusion (X : C) :
    cornerComparison Q F q hp hs X ≫ inclusion Q F q hp hn X =
      mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))) ≫
        comparison Q F q hp hn hs X :=
  (RowRefinement.comparison_naturality _ _ _ _
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (fun _ _ => rfl) (hs (Q.obj X).right.right)
    (DiagramRowInterchange.cone_structure Q F q hp hn hs X)).symm

/-- The actual original diagonal of the four-corner square. -/
abbrev diagonal (X : C) := F.map (Q.obj X).left.hom ≫ F.map (Q.obj X).hom.right

/-- Form the independent seed with the full original source null, including its cone height. -/
def seed (X : C)
    (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
      (diagonal Q F X ≫ cornerComparison Q F q hp hs X)) :
    F.obj (Q.obj X).left.left ⟶ parameterLooping (carrier Q F q hp hn X) :=
  RefinedNullSeed.seed (diagonal Q F X)
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (cornerComparison Q F q hp hs X) (comparison Q F q hp hn hs X)
    (inclusion Q F q hp hn X) (comparison_inclusion Q F q hp hn hs X) K
    (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X)))

/-- The original seed and the independent row seed agree under the actual looped comparison. -/
theorem seed_eq (X : C) (H : Homotopy (diagonal Q F X) (diagonal Q F X))
    (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
      (diagonal Q F X ≫ cornerComparison Q F q hp hs X))
    (hK : K = H.postcomp (cornerComparison Q F q hp hs X)) :
    seed Q F q hp hn hs X K =
      ((H.postcomp (mappingConeInclusion
        (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))).nullLoopMap
          (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X)))) ≫
        parameterLoopingMap (comparison Q F q hp hn hs X) :=
  RefinedNullSeed.seed_eq _ _ _ _ _ _ _ _ H hK

end Quillen.KTheory.Bass.DiagramRowSeed
