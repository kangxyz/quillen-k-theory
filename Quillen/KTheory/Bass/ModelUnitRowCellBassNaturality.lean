/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCellBass

/-! # The independent first Bass-stage cell with its actual row coordinates

Looping the independently descended cone cell and applying the explicit loop/row coordinate
map gives the actual first-stage cell. Its comparison uses the original Bass action and the
computed genuine row comparison, retaining the old loop independently of all row times.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.ModelUnitRowCellCone
open ModelDiagramRowInterchange NaturalTrack
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- The actual first Bass-stage row refinement, with its original index arrows. -/
def bassRefined :=
  DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor))
    (DiagramRowInterchange.bass Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))
    (DiagramRowInterchange.bass_point Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))
    (DiagramRowInterchange.bass_naturality Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))

/-- The original first-stage comparison is natural before taking stable classes. -/
def bassComparisonNatTrans :
    (strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor) ⟶ bassRefined F Q where
  app := bassComparison F Q
  naturality {X Y} g :=
    RowRefinement.comparison_naturality _ _ _ _
      (((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor)).map g)
      (DiagramRowInterchange.bass_naturality Q (F ⋙ prespectrumFunctor)
        (initial F) (initial_point F) (initial_naturality F) g)
      (DiagramRowInterchange.bass_structure Q (F ⋙ prespectrumFunctor)
        (initial F) (initial_point F) (initial_naturality F) (initial_structure F) X)
      (DiagramRowInterchange.bass_structure Q (F ⋙ prespectrumFunctor)
        (initial F) (initial_point F) (initial_naturality F) (initial_structure F) Y)

variable (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The original Bass action's time slice, with both coefficient endpoints fixed. -/
def bassScalarTimeSlice (t : unitInterval) :
    (strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor) ⟶
      L ⋙ (strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor) :=
  diagramHomotopyAt
    (η := Functor.whiskerRight c ((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor)))
    (θ := Functor.whiskerRight c ((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor)))
    (((ofModelUnits L c F unit hunit).bass Q χ hχ).homotopy)
    (((ofModelUnits L c F unit hunit).bass Q χ hχ).naturality) t

/-- Every original time slice of the independently constructed cell is scheme natural. -/
def bassCellTimeSlice (t : unitInterval) :
    (strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor) ⟶ L ⋙ bassRefined F Q where
  app X := (bassCell L c F unit hunit Q χ X).at t
  naturality {X Y} g := by
    rw [bassCell_at_eq L c F unit hunit Q χ hχ X,
      bassCell_at_eq L c F unit hunit Q χ hχ Y]
    exact (bassScalarTimeSlice L c F unit hunit Q χ hχ t ≫
      Functor.whiskerLeft L (bassComparisonNatTrans F Q)).naturality g

end Quillen.KTheory.Bass.ModelUnitRowCellCone
