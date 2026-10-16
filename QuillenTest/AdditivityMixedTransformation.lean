/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.MixedTransformation

/-! Independent original mixed-grid restrictions, exact cut endpoints and full zero cylinders. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Quillen
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.MixedOrdinalCylinder
open scoped Simplicial
universe u v
namespace QuillenTest.AdditivityMixedTransformation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

/-- Each mixed component is the actual original normalized pushout arrow. -/
theorem original_component {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n m) :
    (normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app x =
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app
        ((intervalArrows (firstIndex φ) (switchedIndex φ)
          (firstIndex_le_switchedIndex φ) A).obj x) := rfl

/-- Nerve restriction is independent of the original mixed cut. -/
theorem original_inner {n m m' : SimplexCategory} (ν : m' ⟶ m) (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n m') :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ (𝟙 n) ν).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ
        (gridMap₂ (𝟙 (mixedOrdinal φ)) ν ⋙ A)).app x) :=
  normalizedMixedTransformation_inner V W a a' b b' hs hs' ηF ηG haη ν φ A x

/-- Outer restriction uses the actual cut-dependent mixed ordinal map. -/
theorem original_outer {n n' m : SimplexCategory} (μ : n' ⟶ n) (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n' m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ μ (𝟙 m)).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (μ ≫ φ)
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) (𝟙 m) ⋙ A)).app x) :=
  normalizedMixedTransformation_outer V W a a' b b' hs hs' ηF ηG haη μ φ A x

/-- The zero cut recovers exactly the original identity endpoint transformation. -/
theorem original_zero_cut {n m : SimplexCategory} (A : Grid₂ n m ⥤ C)
    (x : Grid₂ n m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (zeroCut n)
        (gridMap₂ (zeroCollapse n) (𝟙 m) ⋙ A)).app x)
      ((Functor.whiskerLeft (intervalArrows (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')).app x) :=
  normalizedMixedTransformation_zero V W a a' b b' hs hs' ηF ηG haη A x

/-- The one cut recovers the separated-half transformation on the unchanged subdivided input. -/
theorem original_one_cut {n m : SimplexCategory}
    (A : Grid₂ (OrdinalSubdivision.δ.obj n) m ⥤ C) (x : Grid₂ n m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (oneCut n)
        (gridMap₂ (inclusion (oneCut n)) (𝟙 m) ⋙ A)).app x)
      ((Functor.whiskerLeft
        (intervalArrows (Edgewise.left n n) (Edgewise.right n n) (left_le_right n) A)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')).app x) :=
  normalizedMixedTransformation_one V W a a' b b' hs hs' ηF ηG haη A x

/-- The whole cylinder is literally the original nerve cylinder of the actual mixed family. -/
theorem original_nerve_cylinder (hηF : ∀ X, W.weq (ηF.app X))
    (hηG : ∀ X, W.weq (ηG.app X)) (n : SimplexCategoryᵒᵖ)
    (z : (TheoremA.diagonalSSet (outerCylinder (bisimplicialSSet V)) ⊗ Δ[1]).obj n) :
    (((normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h.app n)
        z).1 =
      nerveCylinderDiagram
        (normalizedMixedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n z.1)
        z.2.down := rfl

/-- All mixed cuts and all independent nerve times retain the complete chosen-zero diagram. -/
theorem original_all_cut_zero {n m : SimplexCategory} (φ : Cut n) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ
          ((Functor.const (Grid₂ (mixedOrdinal φ) m)).obj V.zero)) τ =
      (Functor.const (Grid₂ n m)).obj W.zero :=
  normalizedMixedTransformation_nerveCylinder_zero V W a a' b b' hs hs' ηF ηG haη φ τ

end QuillenTest.AdditivityMixedTransformation
