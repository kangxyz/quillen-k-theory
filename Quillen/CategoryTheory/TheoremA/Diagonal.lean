/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.SimplicialReplacement

/-!
# The diagonal simplicial replacement and its canonical comparison maps

This constructs the usual simplicial homotopy-colimit object as the diagonal
of the replacement. No invariance theorem about its realization is built into
the definition.
-/
@[expose] public section


noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

/-- The diagonal of a bisimplicial set. -/
def diagonalSSet (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X

/-- A map of bisimplicial sets gives a map on diagonals. -/
def diagonalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    diagonalSSet X ⟶ diagonalSSet Y :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (Functor.uncurry.map η)

/-- Taking diagonals is functorial on bisimplicial sets. -/
def diagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj X := diagonalSSet X
  map η := diagonalMap η

/-- Interchanging the two simplicial directions does not change the diagonal. -/
def diagonalFlipIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet X.flip ≅ diagonalSSet X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q α
    simp [diagonalSSet])

/-- The diagonal transpose isomorphism is natural in the bisimplicial set. -/
theorem diagonalFlipIso_naturality {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    diagonalMap ((CategoryTheory.flipFunctor _ _ _).map η) ≫ (diagonalFlipIso Y).hom =
      (diagonalFlipIso X).hom ≫ diagonalMap η := by
  ext p x : 4
  rfl

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The Bousfield–Kan simplicial replacement model for the homotopy colimit. -/
def replacementDiagonal : SSet.{u} := diagonalSSet (simplicialReplacement H)

/-- The canonical projection to the nerve of the indexing category. -/
def replacementBaseMap : replacementDiagonal H ⟶ nerve D where
  app p := ↾fun x ↦ x.1
  naturality p q α := by
    ext x : 3
    rfl

section Comma

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- A simplex of the diagonal comma replacement gives a chain of resolution
objects. The bridge arrow at `i` is `F(cᵢ) ⟶ d₀ ⟶ dᵢ`. -/
def commaDiagonalChain (p : SimplexCategoryᵒᵖ)
    (x : Σ σ : ComposableArrows D p.unop.len,
      ComposableArrows (CostructuredArrow F (σ.obj 0)) p.unop.len) :
    ComposableArrows (Resolution F) p.unop.len where
  obj i := ⟨(x.2.obj i).left, x.1.obj i,
    (x.2.obj i).hom ≫ x.1.map (homOfLE (Fin.zero_le i))⟩
  map {i j} f :=
    { left := (x.2.map f).left
      right := x.1.map f
      w := by
        dsimp
        rw [CostructuredArrow.w_assoc]
        rw [Category.assoc, ← x.1.map_comp]
        rfl }
  map_id i := by
    apply Comma.hom_ext
    · exact congrArg (fun k : x.2.obj i ⟶ x.2.obj i ↦ k.left) (x.2.map_id i)
    · simp
  map_comp f g := by
    apply Comma.hom_ext
    · change (x.2.map (f ≫ g)).left = (x.2.map f ≫ x.2.map g).left
      rw [x.2.map_comp]
    · simp

/-- The canonical simplicial map from the diagonal comma replacement to the
nerve of the comma resolution. -/
def commaDiagonalToResolution :
    replacementDiagonal (commaNerveDiagram F) ⟶ nerve (Resolution F) where
  app p := ↾fun x ↦ commaDiagonalChain F p x
  naturality p q α := by
    ext x : 3
    change commaDiagonalChain F q
      ⟨(SimplexCategory.toCat.map α.unop).toFunctor ⋙ x.1,
        (SimplexCategory.toCat.map α.unop).toFunctor ⋙ x.2 ⋙
          CostructuredArrow.map (firstVertexEdge α x.1)⟩ =
      (SimplexCategory.toCat.map α.unop).toFunctor ⋙ commaDiagonalChain F p x
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · dsimp [commaDiagonalChain, firstVertexEdge]
      congr 1
      rw [Category.assoc, ← x.1.map_comp]
      rfl
    · intro i j f
      apply Comma.hom_ext <;> simp [commaDiagonalChain]

/-- Its projection to `D` is the canonical projection of the homotopy-colimit model. -/
theorem commaDiagonalToResolution_target :
    commaDiagonalToResolution F ≫ nerveMap (targetProjection F) =
      replacementBaseMap (commaNerveDiagram F) := by
  ext p x : 4
  rfl

end Comma

end Quillen.TheoremA
