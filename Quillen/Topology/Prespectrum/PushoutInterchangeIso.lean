/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutInterchange

/-!
# The strict inverse and naturality of reduced-pushout interchange

The interchange for the literally transposed span grid is the inverse on all
nine original raw strata. Strict maps of span grids induce original quotient
maps, and these commute with interchange on the same nine strata. No global
coherence, chosen inverse, or additional overlap compatibility is supplied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout.SpanGrid

/-- The two coordinate interchanges compose to the identity on all nine raw strata. -/
theorem interchange_comp_transpose (G : SpanGrid.{u}) :
    G.interchange ≫ G.transpose.interchange = 𝟙 G.iterated := by
  apply hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

/-- Literal coordinate interchange is an isomorphism of the original iterated pushouts. -/
def interchangeIso (G : SpanGrid.{u}) : G.iterated ≅ G.transpose.iterated where
  hom := G.interchange
  inv := G.transpose.interchange
  hom_inv_id := interchange_comp_transpose G
  inv_hom_id := interchange_comp_transpose G.transpose

/-- A map of strict span grids consists only of the nine maps and their twelve local squares. -/
structure Hom (G G' : SpanGrid.{u}) where
  /-- The actual map at each original object. -/
  app (i j : Fin 3) : G.obj i j ⟶ G'.obj i j
  horizontal_left (i : Fin 3) :
    G.horizontalLeft i ≫ app i 1 = app i 0 ≫ G'.horizontalLeft i
  horizontal_right (i : Fin 3) :
    G.horizontalRight i ≫ app i 2 = app i 0 ≫ G'.horizontalRight i
  vertical_left (j : Fin 3) :
    G.verticalLeft j ≫ app 1 j = app 0 j ≫ G'.verticalLeft j
  vertical_right (j : Fin 3) :
    G.verticalRight j ≫ app 2 j = app 0 j ≫ G'.verticalRight j

namespace Hom
variable {G G' : SpanGrid.{u}} (h : Hom G G')

/-- Transpose the same nine component maps and local strict squares. -/
def transpose : Hom G.transpose G'.transpose where
  app i j := h.app j i
  horizontal_left := h.vertical_left
  horizontal_right := h.vertical_right
  vertical_left := h.horizontal_left
  vertical_right := h.horizontal_right

/-- The original quotient map induced on each horizontal row. -/
def rowMap (i : Fin 3) : G.row i ⟶ G'.row i :=
  map (G.horizontalLeft i) (G.horizontalRight i) (G'.horizontalLeft i) (G'.horizontalRight i)
    (h.app i 0) (h.app i 1) (h.app i 2) (h.horizontal_left i) (h.horizontal_right i)

/-- The three left local column squares descend through the entire row cylinder. -/
theorem rowLeft_rowMap : G.rowLeft ≫ h.rowMap 1 = h.rowMap 0 ≫ G'.rowLeft := by
  apply hom_ext
  · apply Quillen.LoopPrespectrum.Hom.ext
    funext n
    ext x
    exact congrArg (left (G'.horizontalLeft 1) (G'.horizontalRight 1) n)
      (congrArg (fun f ↦ f.map n x) (h.vertical_left 1))
  · apply Quillen.LoopPrespectrum.Hom.ext
    funext n
    ext x
    exact congrArg (right (G'.horizontalLeft 1) (G'.horizontalRight 1) n)
      (congrArg (fun f ↦ f.map n x) (h.vertical_left 2))
  · intro n s x
    exact congrArg (fun y ↦ cylinder (G'.horizontalLeft 1) (G'.horizontalRight 1) n (s, y))
      (congrArg (fun f ↦ f.map n x) (h.vertical_left 0))

/-- The three right local column squares descend through the entire row cylinder. -/
theorem rowRight_rowMap : G.rowRight ≫ h.rowMap 2 = h.rowMap 0 ≫ G'.rowRight := by
  apply hom_ext
  · apply Quillen.LoopPrespectrum.Hom.ext
    funext n
    ext x
    exact congrArg (left (G'.horizontalLeft 2) (G'.horizontalRight 2) n)
      (congrArg (fun f ↦ f.map n x) (h.vertical_right 1))
  · apply Quillen.LoopPrespectrum.Hom.ext
    funext n
    ext x
    exact congrArg (right (G'.horizontalLeft 2) (G'.horizontalRight 2) n)
      (congrArg (fun f ↦ f.map n x) (h.vertical_right 2))
  · intro n s x
    exact congrArg (fun y ↦ cylinder (G'.horizontalLeft 2) (G'.horizontalRight 2) n (s, y))
      (congrArg (fun f ↦ f.map n x) (h.vertical_right 0))

/-- The actual iterated original quotient map of a strict span-grid map. -/
def iteratedMap : G.iterated ⟶ G'.iterated :=
  map G.rowLeft G.rowRight G'.rowLeft G'.rowRight
    (h.rowMap 0) (h.rowMap 1) (h.rowMap 2) h.rowLeft_rowMap h.rowRight_rowMap

/-- Interchange is natural for every strict grid map, including the full double overlap. -/
theorem interchange_naturality :
    h.iteratedMap ≫ G'.interchange = G.interchange ≫ h.transpose.iteratedMap := by
  apply hom_ext
  · apply hom_ext
    · apply Quillen.LoopPrespectrum.Hom.ext; funext n; ext x; rfl
    · apply Quillen.LoopPrespectrum.Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · apply hom_ext
    · apply Quillen.LoopPrespectrum.Hom.ext; funext n; ext x; rfl
    · apply Quillen.LoopPrespectrum.Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

end Hom
end Quillen.LoopPrespectrum.HomotopyPushout.SpanGrid
