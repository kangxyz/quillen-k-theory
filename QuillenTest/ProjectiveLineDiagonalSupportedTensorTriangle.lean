/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalSupportedTensorTriangle
public import Mathlib.Data.ZMod.Basic

/-!
# Original diagonal-supported tensor triangle consumers

Check the actual supported vertex, original quotient arrow and connecting
morphism, and the unchanged incidence component of the triangle isomorphism.
Nonreduced and zero-ring instances use the actual negative line.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry DerivedCategory CategoryTheory.Pretriangulated
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
namespace QuillenTest.ProjectiveLineDiagonalSupportedTensorTriangle

open Quillen

/-- The standard original derived category used by the public triangle. -/
local instance supportedTensorStandardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules := HasDerivedCategory.standard _

/-- The third vertex is literally the original diagonal direct image in degree zero. -/
theorem original_supported_vertex (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalSupportedTensorTriangle R E).obj₃ =
      (singleFunctor (relativeSquare R).Modules 0).obj
        ((Scheme.Modules.pushforward (relativeDiagonal R)).obj
          ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))) := rfl

/-- Postcomposing the actual new quotient with the actual inverse recovers the old quotient. -/
theorem original_quotient_recovered (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalSupportedTensorTriangle R E).mor₂ ≫ (diagonalTensorSingleIso R E).inv =
      (diagonalBundleTensorTriangle R E).mor₂ := by
  simp [diagonalSupportedTensorTriangle]

/-- Precomposing the new connecting morphism recovers the original connecting morphism. -/
theorem original_connecting_recovered (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalTensorSingleIso R E).hom ≫ (diagonalSupportedTensorTriangle R E).mor₃ =
      (diagonalBundleTensorTriangle R E).mor₃ := by
  simp [diagonalSupportedTensorTriangle]

/-- The triangle comparison fixes the original incidence endpoints. -/
theorem original_incidence_endpoints (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalSupportedTensorTriangleIso R E).hom.hom₁ = 𝟙 _ ∧
      (diagonalSupportedTensorTriangleIso R E).hom.hom₂ = 𝟙 _ := ⟨rfl, rfl⟩

/-- The genuine negative-line triangle is distinguished over a nonreduced base. -/
theorem nonreduced_supported_triangle :
    diagonalSupportedTensorTriangle (CommRingCat.of (ZMod 4))
      (tautologicalLine (CommRingCat.of (ZMod 4))) ∈
        distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 4))).Modules) :=
  diagonalSupportedTensorTriangle_distinguished _ _

/-- The genuine negative-line triangle remains distinguished over the zero ring. -/
theorem zero_ring_supported_triangle :
    diagonalSupportedTensorTriangle (CommRingCat.of (ZMod 1))
      (tautologicalLine (CommRingCat.of (ZMod 1))) ∈
        distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 1))).Modules) :=
  diagonalSupportedTensorTriangle_distinguished _ _

end QuillenTest.ProjectiveLineDiagonalSupportedTensorTriangle
