/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.SplitSequence
public import Quillen.Waldhausen.SConstruction.Bisimplicial
public import Quillen.Topology.Realization.OrdinalSubdivision

/-! # Genuine coproduct diagrams for the common additivity endpoint -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace Quillen.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]

/-- The pointwise coproduct of two actual quotient diagrams is again a
quotient diagram, proved with actual pushout interchange and gluing. -/
theorem sumGrid_isSimplex₂ {n m : SimplexCategory} {A B : Grid₂ n m ⥤ D}
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B) :
    IsSimplex₂ W.cof W.weq (sumFunctor A B) where
  zero t i := coprod_isZero W (hA.zero t i) (hB.zero t i)
  cofibration t i j k hij hjk := coprod_map_cof W _ _
    (hA.cofibration t i j k hij hjk) (hB.cofibration t i j k hij hjk)
  quotient t i j k hij hjk :=
    isPushout_of_pointwise_pushouts (zeroToFunctor W A) (zeroToFunctor W B)
      (sumInl A B) (sumInr A B) (fun x ↦ coprod_isPushout W (A.obj x) (B.obj x))
      _ _ _ _ (Subsingleton.elim _ _) (by
        change IsPushout (𝟙 W.zero) (𝟙 W.zero) (𝟙 W.zero) (𝟙 W.zero)
        exact IsPushout.of_horiz_isIso ⟨by simp⟩)
      (hA.quotient t i j k hij hjk) (hB.quotient t i j k hij hjk)
  weak s t i j hst hij := coprod_map_weak W _ _
    (hA.weak s t i j hst hij) (hB.weak s t i j hst hij)

/-- The first half commutes with every outer ordinal restriction. -/
theorem gridMap₂_first_naturality {n n' m : SimplexCategory} (μ : n' ⟶ n) :
    gridMap₂ (Edgewise.left n' n') (𝟙 m) ⋙ gridMap₂ (OrdinalSubdivision.δ.map μ) (𝟙 m) =
      gridMap₂ μ (𝟙 m) ⋙ gridMap₂ (Edgewise.left n n) (𝟙 m) := by
  change gridMap₂ (Edgewise.left n' n' ≫ OrdinalSubdivision.δ.map μ) (𝟙 m ≫ 𝟙 m) =
    gridMap₂ (μ ≫ Edgewise.left n n) (𝟙 m ≫ 𝟙 m)
  exact congrArg (fun α ↦ gridMap₂ α (𝟙 m ≫ 𝟙 m)) (OrdinalSubdivision.first.naturality μ).symm

/-- The second half commutes with every outer ordinal restriction. -/
theorem gridMap₂_second_naturality {n n' m : SimplexCategory} (μ : n' ⟶ n) :
    gridMap₂ (Edgewise.right n' n') (𝟙 m) ⋙ gridMap₂ (OrdinalSubdivision.δ.map μ) (𝟙 m) =
      gridMap₂ μ (𝟙 m) ⋙ gridMap₂ (Edgewise.right n n) (𝟙 m) := by
  change gridMap₂ (Edgewise.right n' n' ≫ OrdinalSubdivision.δ.map μ) (𝟙 m ≫ 𝟙 m) =
    gridMap₂ (μ ≫ Edgewise.right n n) (𝟙 m ≫ 𝟙 m)
  exact congrArg (fun α ↦ gridMap₂ α (𝟙 m ≫ 𝟙 m)) (OrdinalSubdivision.second.naturality μ).symm

variable {F H : C ⥤ D}
variable (hH : IsExact V.cof V.weq W.cof W.weq H)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The common endpoint of the original and split mixed deformations. -/
def separatedSumMap : OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨sumFunctor
      (gridMap₂ (Edgewise.left n.unop n.unop) (𝟙 m.unop) ⋙ A.1 ⋙ H)
      (gridMap₂ (Edgewise.right n.unop n.unop) (𝟙 m.unop) ⋙ A.1 ⋙ F),
      sumGrid_isSimplex₂ W
        ((A.2.precomp V.cof V.weq _ _).postcomp V.cof V.weq hH)
        ((A.2.precomp V.cof V.weq _ _).postcomp V.cof V.weq hF)⟩
    naturality _ _ _ := by ext A; rfl }
  naturality n n' μ := by
    ext m A
    apply Subtype.ext
    change sumFunctor
      ((gridMap₂ (Edgewise.left n'.unop n'.unop) (𝟙 m.unop) ⋙
        gridMap₂ (OrdinalSubdivision.δ.map μ.unop) (𝟙 m.unop)) ⋙ A.1 ⋙ H)
      ((gridMap₂ (Edgewise.right n'.unop n'.unop) (𝟙 m.unop) ⋙
        gridMap₂ (OrdinalSubdivision.δ.map μ.unop) (𝟙 m.unop)) ⋙ A.1 ⋙ F) =
      sumFunctor
      ((gridMap₂ μ.unop (𝟙 m.unop) ⋙ gridMap₂ (Edgewise.left n.unop n.unop) (𝟙 m.unop)) ⋙ A.1 ⋙ H)
      ((gridMap₂ μ.unop (𝟙 m.unop) ⋙ gridMap₂ (Edgewise.right n.unop n.unop) (𝟙 m.unop)) ⋙ A.1 ⋙ F)
    rw [gridMap₂_first_naturality, gridMap₂_second_naturality]

end Quillen.Waldhausen.Additivity
