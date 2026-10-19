/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowCellCone
public import Quillen.KTheory.Bass.NaturalTrack

/-! # Independent cone descent of a natural cell into a genuine row refinement

The input is a whole cross-diagram cell, not a Model structure on the later spectrum.
Its four actual corners descend through the original square cone, inverse geometric index,
and forward row strength. The source-null height remains independent of the cell time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Quillen.KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


variable
  (H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
    ((input L c F q hp hn hs).app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
    ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
      ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x))
  (A : NaturalTrack.Track L c F)
  (hcell : ∀ X t, (H X).at t = (A.homotopy X).at t ≫
    (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X))

include hcell in
/-- The whole input comparison identifies natural time slices before taking their cone. -/
theorem timeSlice_eq (t : unitInterval) :
    diagramHomotopyAt (η := input L c F q hp hn hs)
        (θ := input L c F q hp hn hs) H hH t =
      diagramHomotopyAt (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
        A.homotopy A.naturality t ≫
      Functor.whiskerLeft L (DiagramRowRefinement.comparison F q hp hn hs) := by
  apply NatTrans.ext
  funext X
  exact hcell X t

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- The actual cone time slice keeps the original index and strength maps. -/
theorem cone_at (X : C) (t : unitInterval) :
    (cone L c F q hp hn hs H hH Q χ X).at t =
      (ConeTrack.map Q (diagramHomotopyAt (η := input L c F q hp hn hs)
        (θ := input L c F q hp hn hs) H hH t)).app X ≫
      ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X ≫
        DiagramConeRowStrength.strength Q F q hp hn (L.obj X)) :=
  congrArg (fun f => f ≫
    ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X ≫
      DiagramConeRowStrength.strength Q F q hp hn (L.obj X)))
    ((square L c F q hp hn hs H hH (Q.obj X)).cone_at t)

/-- The computed genuine row comparison on the original cone. -/
def coneComparison (X : C) :=
  RowRefinement.comparison ((ConeTrack.diagram Q F).obj X)
    (DiagramRowInterchange.cone Q F q hp hn X)
    (DiagramRowInterchange.cone_point Q F q hp hn X)
    (DiagramRowInterchange.cone_structure Q F q hp hn hs X)

variable (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

include hcell in
/-- Independent descent preserves a proved whole-cell comparison through the original cone. -/
theorem cone_at_eq (X : C) (t : unitInterval) :
    (cone L c F q hp hn hs H hH Q χ X).at t =
      ((A.cone Q χ hχ).homotopy X).at t ≫
        coneComparison F q hp hn hs Q (L.obj X) := by
  rw [cone_at, timeSlice_eq L c F q hp hn hs H hH A hcell,
    LoopConeTrack.coneMap_comp]
  change _ = (ConeTrack.action Q L c χ hχ F A.homotopy A.naturality X).at t ≫ _
  rw [ConeTrack.action_at]
  simp only [NatTrans.comp_app]
  let a := (ConeTrack.map Q (diagramHomotopyAt
    (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
    A.homotopy A.naturality t)).app X
  let b := (ConeTrack.map Q (Functor.whiskerLeft L
    (DiagramRowRefinement.comparison F q hp hn hs))).app X
  let j := (ConeTrack.indexMap Q L χ F).app X
  let j' := (ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X
  let d := (ConeTrack.map Q (DiagramRowRefinement.comparison F q hp hn hs)).app (L.obj X)
  let s := DiagramConeRowStrength.strength Q F q hp hn (L.obj X)
  have hi : b ≫ j' = j ≫ d := LoopConeTrack.indexMap_naturality Q L χ
    (DiagramRowRefinement.comparison F q hp hn hs) X
  have ht : d ≫ s = coneComparison F q hp hn hs Q (L.obj X) :=
    DiagramConeRowStrength.strength_comparison Q F q hp hn hs (L.obj X)
  change (a ≫ b) ≫ (j' ≫ s) = (a ≫ j) ≫ coneComparison F q hp hn hs Q (L.obj X)
  calc
    (a ≫ b) ≫ (j' ≫ s) = a ≫ ((b ≫ j') ≫ s) :=
      (Category.assoc a b (j' ≫ s)).trans
        (congrArg (fun z => a ≫ z) (Category.assoc b j' s).symm)
    _ = a ≫ ((j ≫ d) ≫ s) := by rw [hi]
    _ = (a ≫ j) ≫ (d ≫ s) :=
      (congrArg (fun z => a ≫ z) (Category.assoc j d s)).trans
        (Category.assoc a j (d ≫ s)).symm
    _ = (a ≫ j) ≫ coneComparison F q hp hn hs Q (L.obj X) := by rw [ht]

end Quillen.KTheory.Bass.DiagramRowCell
