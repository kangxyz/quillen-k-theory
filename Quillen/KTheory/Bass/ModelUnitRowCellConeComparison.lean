/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCellCone

/-! # Whole first-cone comparison of independent Model-unit cells

The independent four-corner cell construction agrees, at every original time, with the original
cone action followed by the genuine row comparison. This uses the actual forward strength
triangle and the inverse geometric index map, with no compatibility or stability assumption.
-/
@[expose] public section
noncomputable section
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

/-- Every original time slice of the independent initial cell has the actual row comparison. -/
theorem cellTimeSlice_eq (t : unitInterval) :
    diagramHomotopyAt (η := input L c F) (θ := input L c F)
      (initialCell L c F unit) (initialCell_naturality L c F unit hunit) t =
    diagramHomotopyAt
        (η := Functor.whiskerRight c (F ⋙ prespectrumFunctor))
        (θ := Functor.whiskerRight c (F ⋙ prespectrumFunctor))
        (ofModelUnits L c F unit hunit).homotopy
        (ofModelUnits L c F unit hunit).naturality t ≫
      Functor.whiskerLeft L (comparison F) := by
  apply NatTrans.ext
  funext X
  rfl

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- Every time slice is the actual moving-square cone followed by index transport and strength. -/
theorem coneCell_at (X : C) (t : unitInterval) :
    (coneCell L c F unit hunit Q χ X).at t =
      (ConeTrack.map Q (diagramHomotopyAt (η := input L c F) (θ := input L c F)
        (initialCell L c F unit) (initialCell_naturality L c F unit hunit) t)).app X ≫
      ((ConeTrack.indexMap Q L χ (refined F)).app X ≫
        DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
          (initial F) (initial_point F) (initial_naturality F) (L.obj X)) :=
  congrArg (fun f => f ≫ ((ConeTrack.indexMap Q L χ (refined F)).app X ≫
    DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (L.obj X)))
    ((squareCell L c F unit hunit (Q.obj X)).cone_at t)

/-- The actual first-cone row comparison, using its computed original interchange. -/
def coneComparison (X : C) :=
  RowRefinement.comparison ((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X)
    (DiagramRowInterchange.cone Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) X)
    (DiagramRowInterchange.cone_point Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) X)
    (DiagramRowInterchange.cone_structure Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (initial_structure F) X)

variable (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The independent whole cell equals the original cone action through the actual row roof. -/
theorem coneCell_at_eq (X : C) (t : unitInterval) :
    (coneCell L c F unit hunit Q χ X).at t =
      (ConeTrack.action Q L c χ hχ (F ⋙ prespectrumFunctor)
        (ofModelUnits L c F unit hunit).homotopy
        (ofModelUnits L c F unit hunit).naturality X).at t ≫
      coneComparison F Q (L.obj X) := by
  rw [coneCell_at, cellTimeSlice_eq L c F unit hunit,
    LoopConeTrack.coneMap_comp, ConeTrack.action_at]
  simp only [NatTrans.comp_app]
  let a := (ConeTrack.map Q (diagramHomotopyAt
    (η := Functor.whiskerRight c (F ⋙ prespectrumFunctor))
    (θ := Functor.whiskerRight c (F ⋙ prespectrumFunctor))
    (ofModelUnits L c F unit hunit).homotopy
    (ofModelUnits L c F unit hunit).naturality t)).app X
  let b := (ConeTrack.map Q (Functor.whiskerLeft L (comparison F))).app X
  let j := (ConeTrack.indexMap Q L χ (F ⋙ prespectrumFunctor)).app X
  let j' := (ConeTrack.indexMap Q L χ (refined F)).app X
  let d := (ConeTrack.map Q (comparison F)).app (L.obj X)
  let s := DiagramConeRowStrength.strength Q (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) (L.obj X)
  have hi : b ≫ j' = j ≫ d := LoopConeTrack.indexMap_naturality Q L χ (comparison F) X
  have hs : d ≫ s = coneComparison F Q (L.obj X) :=
    DiagramConeRowStrength.strength_comparison Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (initial_structure F) (L.obj X)
  change (a ≫ b) ≫ (j' ≫ s) = (a ≫ j) ≫ coneComparison F Q (L.obj X)
  calc
    (a ≫ b) ≫ (j' ≫ s) = a ≫ ((b ≫ j') ≫ s) :=
      (Category.assoc a b (j' ≫ s)).trans
        (congrArg (fun z => a ≫ z) (Category.assoc b j' s).symm)
    _ = a ≫ ((j ≫ d) ≫ s) := by rw [hi]
    _ = (a ≫ j) ≫ (d ≫ s) :=
      (congrArg (fun z => a ≫ z) (Category.assoc j d s)).trans
        (Category.assoc a j (d ≫ s)).symm
    _ = (a ≫ j) ≫ coneComparison F Q (L.obj X) := by rw [hs]

end Quillen.KTheory.Bass.ModelUnitRowCellCone
