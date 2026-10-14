/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.RectangleOuterBinaryRow

/-! The initial native binary row of the original rectangle, with the actual precomposition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {V : Model.{u + 1}} {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (F : V ⟶ modelOf (boundedFlatPerfectWaldhausen C'))
  (P : V ⟶ modelOf (boundedFlatPerfectWaldhausen A))
  (ρ : F.functor ≅ (P ≫ NormalizedTripleSimplex.sourceMap c q p).functor)

def initialIndex : Fin 3 → Fin 18 := ![0, 1, 2]

def rectangleInitialReference : F.functor ≅
    (P ≫ BinaryNormalizationSimplex.sourceMap c (q ≫ p)).functor := ρ

theorem rectangle_initial_functor (i : Fin 3) :
    (preRectangleNodes p q p' q' a b c hp hq F P ρ (initialIndex i)).1.functor =
      (preBinaryNodes F P c (q ≫ p) (rectangleInitialReference p q c F P ρ) i).1.functor := by
  fin_cases i <;> rfl

/-- The actual initial source, raw intermediate and normalized target retain both native pieces. -/
theorem rectangle_initial_row (i : Fin 3) :
    preRectangleNodes p q p' q' a b c hp hq F P ρ (initialIndex i) =
      preBinaryNodes F P c (q ≫ p) (rectangleInitialReference p q c F P ρ) i := by
  fin_cases i <;>
    apply Sigma.ext (Model.Hom.ext (rectangle_initial_functor p q p' q' a b c hp hq F P ρ _)) <;>
    exact heq_of_eq rfl

end Quillen.PerfectComplexes.BassH0Merge
