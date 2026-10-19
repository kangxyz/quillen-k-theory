/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.StructureHomotopy

/-!
# Finite S-construction of a transformation followed by a first row

Apply each original finite S-construction to a weak natural transformation after the actual
one-row insertion. These independently specified simplex functions assemble to the double
cylinder. The whole result agrees with the original transformation cylinder followed by the
original row cylinder, retaining both interval coordinates in their specified order.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

/-- Apply the genuine finite S-construction after the actual first-row insertion. -/
def rowTransformationSimplex (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    ((stages (k + 1)).obj W).obj n :=
  stageTransformationFunction k
    (F := F ≫ (insertion θ.down).app W) (G := G ≫ (insertion θ.down).app W)
    (whiskerRight η ((insertion θ.down).app W).functor)
    (fun B => ((insertion θ.down).app W).exact.weak _ (hη B)) n A τ

/-- Finite S-prolongation preserves the whole transformation/first-row composite. -/
theorem rowTransformationSimplex_eq (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages k).obj V).obj n) (τ θ : (Δ[1]).obj n) :
    rowTransformationSimplex η hη k n A τ θ =
      (stageCylinder k W).app n (stageTransformationFunction k η hη n A τ, θ) :=
  stageTransformationFunction_postcomp k η hη ((insertion θ.down).app W) n A τ

/-- The original entrywise row-transformation cells assemble under all diagonal operators. -/
def rowTransformationCylinder (k : ℕ) :
    (((stages k).obj V) ⊗ Δ[1]) ⊗ Δ[1] ⟶ (stages (k + 1)).obj W where
  app n := ↾fun z => rowTransformationSimplex η hη k n z.1.1 z.1.2 z.2
  naturality n m α := by
    let H := (stageTransformationCylinder k η hη ▷ Δ[1]) ≫ stageCylinder k W
    have h (q : SimplexCategoryᵒᵖ) :
        (↾fun z : ((((stages k).obj V) ⊗ Δ[1]) ⊗ Δ[1]).obj q =>
          rowTransformationSimplex η hη k q z.1.1 z.1.2 z.2) = H.app q := by
      apply ConcreteCategory.hom_ext
      intro z
      exact rowTransformationSimplex_eq η hη k q z.1.1 z.1.2 z.2
    rw [h m, h n]
    exact H.naturality α

/-- The whole double cylinder agrees with the original ordered composite. -/
theorem rowTransformationCylinder_eq (k : ℕ) :
    rowTransformationCylinder η hη k =
      (stageTransformationCylinder k η hη ▷ Δ[1]) ≫ stageCylinder k W := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact rowTransformationSimplex_eq η hη k n z.1.1 z.1.2 z.2

end Quillen.Waldhausen.IteratedS
