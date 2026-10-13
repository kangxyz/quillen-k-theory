/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalTensorTriangle
public import Mathlib.Data.ZMod.Basic

/-!
# Original-map consumers of the affine-base diagonal tensor triangle

The consumers inspect both original derived arrows, the actual coefficient map
and its connecting-arrow compatibility, and the original pulled-back retraction.
Nonreduced and zero-ring cases retain the same geometric constructions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open DerivedCategory CategoryTheory.Pretriangulated
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine

namespace QuillenTest.ProjectiveLineDiagonalTensorTriangle

open Quillen

/-- The original standard ambient derived category, as used by the public triangle. -/
local instance standardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules :=
  HasDerivedCategory.standard _

/-- The first derived arrow is the original tensor incidence and the second the adjoint quotient. -/
theorem original_triangle_arrows (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    (diagonalTensorTriangle R M).mor₁ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M)).map
        (diagonalIncidence R)) ∧
    (diagonalTensorTriangle R M).mor₂ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M)).map
        (diagonalQuotientMap R)) := ⟨rfl, rfl⟩

/-- The middle component retains the original pulled-back coefficient arrow
and original quotient. -/
theorem original_coefficient_triangle_map (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [IsFiniteLocallyFree (Spec R) M]
    [IsFiniteLocallyFree (Spec R) N] (f : M ⟶ N) :
    (diagonalTensorTriangleMap R f).hom₂ =
      (singleFunctor (relativeSquare R).Modules 0).map
        ((moduleTensorCoefficientMap (relativeSquare R)
          ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).map f)).app
          ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))) := rfl

/-- The actual connecting arrow is natural for the original coefficient triangle map. -/
theorem original_connecting_square (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [IsFiniteLocallyFree (Spec R) M]
    [IsFiniteLocallyFree (Spec R) N] (f : M ⟶ N) :
    (diagonalTensorTriangleMap R f).hom₃ ≫ (diagonalTensorTriangle R N).mor₃ =
      (diagonalTensorTriangle R M).mor₃ ≫
        (shiftFunctor (DerivedCategory (relativeSquare R).Modules) (1 : ℤ)).map
          (diagonalTensorTriangleMap R f).hom₁ :=
  (diagonalTensorTriangleMap R f).comm₃.symm

/-- The actual triangle maps preserve identity and composition of original coefficient arrows. -/
theorem original_triangle_functoriality (R : CommRingCat.{u})
    {M N P : (Spec R).Modules} [IsFiniteLocallyFree (Spec R) M]
    [IsFiniteLocallyFree (Spec R) N] [IsFiniteLocallyFree (Spec R) P]
    (f : M ⟶ N) (g : N ⟶ P) :
    diagonalTensorTriangleMap R (𝟙 M) = 𝟙 (diagonalTensorTriangle R M) ∧
      diagonalTensorTriangleMap R (f ≫ g) =
        diagonalTensorTriangleMap R f ≫ diagonalTensorTriangleMap R g :=
  ⟨diagonalTensorTriangleMap_id R M, diagonalTensorTriangleMap_comp R f g⟩

/-- The literal pulled-back inclusion and projection retain the original finite-free isomorphism. -/
theorem original_pullback_retraction {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {I : Type u}
    (h : Retract M (SheafOfModules.free (R := Y.ringCatSheaf) I)) :
    ((Scheme.Modules.pullback f).map h.i ≫ (pullbackFreeIso f I).hom) ≫
      ((pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map h.r) =
        𝟙 ((Scheme.Modules.pullback f).obj M) :=
  (pullbackFiniteFreeRetract f h).retract

/-- The actual tensor quotient remains a cokernel without supplying a chosen coefficient retract. -/
def originalTensorQuotient (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    IsColimit (CokernelCofork.ofπ (diagonalTensorSequence R M).g
      (diagonalTensorSequence R M).zero) := by
  have h := diagonalTensorSequence_shortExact R M
  have := h.epi_g
  exact h.exact.gIsCokernel

/-- A nonreduced affine base supports the original distinguished tensor triangle. -/
theorem nonreduced_original_triangle :
    diagonalTensorTriangle (CommRingCat.of (ZMod 4))
      (SheafOfModules.free
        (R := (Spec (CommRingCat.of (ZMod 4))).ringCatSheaf) (Fin 2)) ∈
      distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 4))).Modules) :=
  diagonalTensorTriangle_distinguished _ _

/-- The same original tensor sequence is short exact over the zero ring. -/
theorem zeroRing_original_tensor_sequence :
    (diagonalTensorSequence (CommRingCat.of (ZMod 1))
      (SheafOfModules.free
        (R := (Spec (CommRingCat.of (ZMod 1))).ringCatSheaf) (Fin 1))).ShortExact :=
  diagonalTensorSequence_shortExact _ _

end QuillenTest.ProjectiveLineDiagonalTensorTriangle
