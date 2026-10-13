/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareMapHomotopy
public import Quillen.KTheory.Bass.StrictDiagramZeroMap

/-!
# The actual Bass action on coefficient-natural whole homotopies

A family of original whole prespectrum homotopies which is strictly coefficient-natural
at every time gives a whole homotopy of the existing Bass diagram maps. Its time slices are
the images of the original time-slice natural transformations. Hence the resulting family
is again strictly coefficient-natural, with all original interval coordinates retained.

For an original null track, the initial endpoint uses the actual functor composition law
and the final endpoint uses the proved literal Bass-zero equality. No value of the zero
diagram is identified with a point object. Comparison with the original seed-relative
pasting is a separate obligation.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C]

/-- The unchanged iterated arrow-functor component on an original natural transformation. -/
def diagramSquareMap {F G : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ G)
    (S : Arrow (Arrow C)) : F.mapArrow.mapArrow.obj S ⟶ G.mapArrow.mapArrow.obj S :=
  ((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map η)).app S

variable {F G : C ⥤ LoopPrespectrum.{w}} {η θ : F ⟶ G}
    (H : ∀ X, Homotopy (η.app X) (θ.app X))
    (hH : ∀ {X Y} (f : X ⟶ Y) n r x,
      (G.map f).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map f).map n x))

/-- Each original homotopy time is an actual strict natural transformation of diagrams. -/
def diagramHomotopyAt (r : unitInterval) : F ⟶ G where
  app X := (H X).at r
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact (hH f n r x).symm

/-- The four original corner tracks satisfy the exact moving strict-square equations. -/
def diagramSquareMapHomotopy (S : Arrow (Arrow C)) :
    StrictSquare.MapHomotopy (diagramSquareMap η S) (diagramSquareMap θ S) where
  source := H S.left.left
  upper := H S.left.right
  lower := H S.right.left
  target := H S.right.right
  commUpper n r x := (hH S.left.hom n r x).symm
  commLower n r x := (hH S.hom.left n r x).symm
  commRight n r x := (hH S.hom.right n r x).symm
  commBottom n r x := (hH S.right.hom n r x).symm

/-- The same actual natural transformation gives every strict square time slice. -/
theorem diagramSquareMapHomotopy_at (S : Arrow (Arrow C)) (r : unitInterval) :
    (diagramSquareMapHomotopy H hH S).at r = diagramSquareMap (diagramHomotopyAt H hH r) S := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> rfl

/-- The original moving span, cone and loop maps give the whole Bass homotopy. -/
def strictDiagramMapHomotopy (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    Homotopy (((strictDiagramFunctor Q).map η).app X)
      (((strictDiagramFunctor Q).map θ).app X) :=
  (diagramSquareMapHomotopy H hH (Q.obj X)).looped

/-- Each actual time slice is the unchanged Bass image of the original time-slice map. -/
theorem strictDiagramMapHomotopy_at (Q : C ⥤ Arrow (Arrow C)) (X : C) (r : unitInterval) :
    (strictDiagramMapHomotopy H hH Q X).at r =
      ((strictDiagramFunctor Q).map (diagramHomotopyAt H hH r)).app X := by
  change (diagramSquareMapHomotopy H hH (Q.obj X)).looped.at r = _
  rw [StrictSquare.MapHomotopy.looped_at, diagramSquareMapHomotopy_at]
  rfl

/-- The entire Bass image remains strictly coefficient-natural at the identical time. -/
theorem strictDiagramMapHomotopy_naturality (Q : C ⥤ Arrow (Arrow C))
    {X Y : C} (f : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space n) :
    (((strictDiagramFunctor Q).obj G).map f).map n
        ((strictDiagramMapHomotopy H hH Q X).level n (r, x)) =
      (strictDiagramMapHomotopy H hH Q Y).level n
        (r, (((strictDiagramFunctor Q).obj F).map f).map n x) := by
  change ((strictDiagramMapHomotopy H hH Q X).at r ≫
      ((strictDiagramFunctor Q).obj G).map f).map n x =
    (((strictDiagramFunctor Q).obj F).map f ≫
      (strictDiagramMapHomotopy H hH Q Y).at r).map n x
  rw [strictDiagramMapHomotopy_at, strictDiagramMapHomotopy_at]
  exact congrArg (fun k => k.map n x)
    (((strictDiagramFunctor Q).map (diagramHomotopyAt H hH r)).naturality f).symm

section Null
variable {K : C ⥤ LoopPrespectrum.{w}} (i : F ⟶ G) (c : G ⟶ K)
    (N : ∀ X, Homotopy ((i ≫ c).app X) ((diagramZeroMap F K).app X))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (F.map f).map n x))

/-- The actual Bass nullhomotopy, with both endpoints identified by proved original-map laws. -/
def strictDiagramNullHomotopy (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    Homotopy ((((strictDiagramFunctor Q).map i).app X) ≫
      (((strictDiagramFunctor Q).map c).app X))
      (zeroHom (((strictDiagramFunctor Q).obj F).obj X)
        (((strictDiagramFunctor Q).obj K).obj X)) :=
  (strictDiagramMapHomotopy N hN Q X).cast
    (congrArg (fun α => α.app X) ((strictDiagramFunctor Q).map_comp i c))
    (strictDiagramFunctor_map_zero_app Q F K X)

/-- Normalizing the two endpoint witnesses changes no value of the whole Bass null track. -/
theorem strictDiagramNullHomotopy_level (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ) :
    (strictDiagramNullHomotopy i c N hN Q X).level n =
      (strictDiagramMapHomotopy N hN Q X).level n := rfl

end Null
end Quillen.KTheory.Bass
