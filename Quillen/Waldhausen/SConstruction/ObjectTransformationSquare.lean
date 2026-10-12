/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.OneRowTransformation
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCylinder
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformation
public import Quillen.Waldhausen.SConstruction.BisimplexRealization

/-! # The original transformation cylinder on the actual object simplex

The exact functors' chosen-zero equations identify the whole original object cylinder with
the existing weak-arrow square of the actual transformation component. Both simplex operators
remain independent, including every mixed map and its original naturality equation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF0 hG0 in
/-- The entire original transformation cylinder on an object is its original weak-arrow square. -/
theorem objectTransformationCylinder_square (A : C) :
    SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A) ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W hF hG η hη =
      bisimplexFamily W (W.weakObjectSimplex (η.app A) (hη A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (η.app A) (hη A)).property) := by
  ext n z
  apply Subtype.ext
  let J := Structure.intervalProjection n.unop ⋙ indexMap z.1.down
  change nerveCylinderDiagram (whiskerLeft (J ⋙ oneDiagram V A) η) z.2.down =
    gridMap₂ z.1.down z.2.down ⋙ (W.weakObjectSimplex (η.app A) (hη A)).val
  calc
    _ = nerveCylinderDiagram
        (whiskerLeft J ((oneEmbedding W).map (η.app A)).hom) z.2.down := by
      apply nerveCylinderDiagram_congr_app
      · change (J ⋙ oneDiagram V A) ⋙ F = J ⋙ oneDiagram W (F.obj A)
        rw [Functor.assoc, oneDiagram_postcompose V W hF hF0]
      · change (J ⋙ oneDiagram V A) ⋙ G = J ⋙ oneDiagram W (G.obj A)
        rw [Functor.assoc, oneDiagram_postcompose V W hG hG0]
      · intro p
        exact oneDiagram_transformation_app V W hF η hF0 hG0 A (J.obj p)
    _ = _ := W.weakObjectSimplex_cylinder (η.app A) (hη A) z.1.down z.2.down

end Quillen.Waldhausen
