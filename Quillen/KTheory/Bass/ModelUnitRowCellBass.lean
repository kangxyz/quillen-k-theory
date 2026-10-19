/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCellConeComparison
public import Quillen.KTheory.Bass.DiagramBassRowStrength

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

private theorem loopMap_comp {E E' E'' : LoopPrespectrum.{w}}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    parameterLoopingMap (f ≫ g) = parameterLoopingMap f ≫ parameterLoopingMap g :=
  parameterLoopingFunctor.map_comp f g

variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)) ≅ 𝟭 (F.obj (L.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (F.map (L.map g)).functor (unit X) (unit Y))
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- The actual inverse row/old-loop coordinate map at the original cone. -/
def loopRowInverse (X : C) :=
  RowRefinement.parameterLoopingInverse ((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X)
    (DiagramRowInterchange.cone Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) X)
    (DiagramRowInterchange.cone_point Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) X)

/-- The independent first Bass-stage cell loops the actual cone construction. -/
def bassCell (X : C) :=
  ((coneCell L c F unit hunit Q χ X).parameterLooping).postcomp
    (loopRowInverse F Q (L.obj X))

/-- The positive cell keeps unit time, distinguished row and old loop independent. -/
theorem bassCell_succ (X : C) (k : ℕ) (r s t : unitInterval)
    (γ : Path (((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X).point (k + 1))
      (((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X).point (k + 1))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((bassCell L c F unit hunit Q χ X).level (k + 1) (r, γ)) s) t =
    Path.toContinuousMap
      ((coneCell L c F unit hunit Q χ X).level (k + 1) (r, γ t)) s := rfl

/-- Degree zero keeps both new row coordinates separate from the original old loop. -/
theorem bassCell_zero (X : C) (u r s t : unitInterval)
    (γ : Path (((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X).point 0)
      (((ConeTrack.diagram Q (F ⋙ prespectrumFunctor)).obj X).point 0)) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((bassCell L c F unit hunit Q χ X).level 0 (u, γ)) r) s) t =
    Path.toContinuousMap (Path.toContinuousMap
      ((coneCell L c F unit hunit Q χ X).level 0 (u, γ t)) r) s := rfl

/-- The genuine computed first-stage row comparison. -/
def bassComparison (X : C) :=
  (DiagramRowRefinement.comparison ((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor))
    (DiagramRowInterchange.bass Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))
    (DiagramRowInterchange.bass_point Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))
    (DiagramRowInterchange.bass_naturality Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F))
    (DiagramRowInterchange.bass_structure Q (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (initial_structure F))).app X

/-- Both structure coordinates survive the actual old-loop/row conversion. -/
theorem loopRow_comparison (X : C) :
    parameterLoopingMap (coneComparison F Q X) ≫ loopRowInverse F Q X =
      bassComparison F Q X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    apply Path.ext; funext r
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl
  | succ k =>
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl

variable (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Every original time slice is the original first Bass action through its genuine row roof. -/
theorem bassCell_at_eq (X : C) (t : unitInterval) :
    (bassCell L c F unit hunit Q χ X).at t =
      (((ofModelUnits L c F unit hunit).bass Q χ hχ).homotopy X).at t ≫
        bassComparison F Q (L.obj X) := by
  change ((coneCell L c F unit hunit Q χ X).parameterLooping).at t ≫
      loopRowInverse F Q (L.obj X) = _
  rw [Homotopy.parameterLooping_at, coneCell_at_eq L c F unit hunit Q χ hχ,
    loopMap_comp, Category.assoc, loopRow_comparison]
  rfl

end Quillen.KTheory.Bass.ModelUnitRowCellCone
