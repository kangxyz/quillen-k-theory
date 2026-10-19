/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.ModelUnitRowCellIteration

/-! # Symbolic-stage coordinate and source-null regression

The actual recursively constructed cell at stage `i` is fed to the independent next cone/loop
operation. The old input loop, row coordinates, unit time and original null height stay separate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.ModelUnitRowCellIteration
open Quillen.KTheory.Bass ModelDiagramRowInterchange
open NaturalTrack
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

private abbrev finiteDiagram (i : ℕ) :=
  (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)

private def nextCone (i : ℕ) (X : C) :=
  DiagramRowCell.cone L c (finiteDiagram F Q i)
    (stage Q F i) (stage_point Q F i) (stage_naturality Q F i) (stage_structure Q F i)
    (iteratedCell L c F unit hunit Q χ hχ i)
    (iteratedCell_naturality L c F unit hunit Q χ hχ i) Q χ X

private def nextCell (i : ℕ) (X : C) :=
  DiagramRowCell.rawBass L c (finiteDiagram F Q i)
    (stage Q F i) (stage_point Q F i) (stage_naturality Q F i) (stage_structure Q F i)
    (iteratedCell L c F unit hunit Q χ hχ i)
    (iteratedCell_naturality L c F unit hunit Q χ hχ i) Q χ X

/-- At every symbolic Bass stage the old input-loop time is independent of the row and unit. -/
theorem positive_coordinates (i : ℕ) (X : C) (k : ℕ) (r s t : unitInterval)
    (γ : Path (((ConeTrack.diagram Q (finiteDiagram F Q i)).obj X).point (k + 1))
      (((ConeTrack.diagram Q (finiteDiagram F Q i)).obj X).point (k + 1))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((nextCell L c F unit hunit Q χ hχ i X).level (k + 1) (r, γ)) s) t =
    Path.toContinuousMap
      ((nextCone L c F unit hunit Q χ hχ i X).level (k + 1) (r, γ t)) s := rfl

/-- Degree zero keeps both row times and the additional old loop at every symbolic stage. -/
theorem zero_coordinates (i : ℕ) (X : C) (v r s t : unitInterval)
    (γ : Path (((ConeTrack.diagram Q (finiteDiagram F Q i)).obj X).point 0)
      (((ConeTrack.diagram Q (finiteDiagram F Q i)).obj X).point 0)) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((nextCell L c F unit hunit Q χ hχ i X).level 0 (v, γ)) r) s) t =
    Path.toContinuousMap (Path.toContinuousMap
      ((nextCone L c F unit hunit Q χ hχ i X).level 0 (v, γ t)) r) s := rfl

/-- The original null height stays unchanged through the actual symbolic-stage cone cell. -/
theorem source_null (i : ℕ) (X : C) (n : ℕ) (r s : unitInterval)
    (x : ((finiteDiagram F Q i).obj (Q.obj X).left.left).space n) :
    (nextCone L c F unit hunit Q χ hχ i X).level n
        (r, (StrictSquare.sourceNullHomotopy
          ((finiteDiagram F Q i).mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (DiagramConeRowStrength.strength Q (finiteDiagram F Q i)
        (stage Q F i) (stage_point Q F i) (stage_naturality Q F i) (L.obj X)).map n
        ((StrictSquare.sourceNullHomotopy
          ((DiagramRowRefinement.diagram (finiteDiagram F Q i)
            (stage Q F i) (stage_point Q F i) (stage_naturality Q F i)).mapArrow.mapArrow.obj
              (Q.obj (L.obj X)))).level n
          (s, ((DiagramRowRefinement.diagram (finiteDiagram F Q i)
            (stage Q F i) (stage_point Q F i) (stage_naturality Q F i)).map
              (χ.inv.app X).left.left).map n
                ((iteratedCell L c F unit hunit Q χ hχ i (Q.obj X).left.left).level n (r, x)))) :=
  DiagramRowCell.cone_sourceNull L c (finiteDiagram F Q i)
    (stage Q F i) (stage_point Q F i) (stage_naturality Q F i) (stage_structure Q F i)
    (iteratedCell L c F unit hunit Q χ hχ i)
    (iteratedCell_naturality L c F unit hunit Q χ hχ i) Q χ X n r s x

end QuillenTest.ModelUnitRowCellIteration
