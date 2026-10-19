/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowCellIteration
public import Quillen.KTheory.Bass.ModelUnitRowCellNaturality
public import Quillen.KTheory.Bass.ModelDiagramRowInterchange

/-! # Actual independent Model-unit cells at every original Bass stage

The genuine initial first-row cell and its proved whole comparison are the only initial data.
Every later cell is constructed by finite square/cone/index/loop descent. The conclusion uses
the original stage track and the computed actual row refinement, with no extra compatibility.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowInterchange
open NaturalTrack
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))

/-- The actual initial cell has its proved index naturality and whole row comparison. -/
def initialCellFamily :
    DiagramRowCell.Family L c (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (initial_structure F)
      (ofModelUnits L c F unit hunit) :=
  ⟨initialCell L c F unit, initialCell_naturality L c F unit hunit, fun _ _ => rfl⟩

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Iterate the actual cell construction on the original Bass diagrams and computed row maps. -/
def iteratedCellFamily (i : ℕ) :=
  DiagramRowCell.iterateFamily L c Q χ hχ i (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) (initial_structure F)
    (ofModelUnits L c F unit hunit) (initialCellFamily L c F unit hunit)

/-- The independent whole cell at Bass stage `i`, not spectrum level `i`. -/
def iteratedCell (i : ℕ) (X : C) :=
  (iteratedCellFamily L c F unit hunit Q χ hχ i).val X

/-- Every original time slice recovers the original current-stage action through its row map. -/
theorem iteratedCell_at_eq (i : ℕ) (X : C) (t : unitInterval) :
    (iteratedCell L c F unit hunit Q χ hχ i X).at t =
      (((ofModelUnits L c F unit hunit).stages Q χ hχ i).homotopy X).at t ≫
        (DiagramRowRefinement.comparison ((strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)) (stage Q F i) (stage_point Q F i)
          (stage_naturality Q F i) (stage_structure Q F i)).app (L.obj X) :=
  (iteratedCellFamily L c F unit hunit Q χ hχ i).property.2 X t

/-- The actual finite cell is natural at its unchanged unit time and every spectrum level. -/
theorem iteratedCell_naturality (i : ℕ) {X Y : C} (g : X ⟶ Y) (n : ℕ)
    (t : unitInterval)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space n) :
    ((DiagramRowRefinement.diagram ((strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor)) (stage Q F i) (stage_point Q F i)
      (stage_naturality Q F i)).map (L.map g)).map n
        ((iteratedCell L c F unit hunit Q χ hχ i X).level n (t, x)) =
      (iteratedCell L c F unit hunit Q χ hχ i Y).level n
        (t, (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map n x) :=
  (iteratedCellFamily L c F unit hunit Q χ hχ i).property.1 g n t x

end Quillen.KTheory.Bass.ModelDiagramRowInterchange
