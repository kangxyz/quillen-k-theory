/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalBundleTensorTriangle
public import Mathlib.Data.ZMod.Basic

/-!
# Original-map consumers of the projective-line bundle tensor triangle

The consumers inspect both original derived arrows, the actual coefficient map
and its connecting-arrow compatibility, and general locally free tensor kernels.
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

namespace QuillenTest.ProjectiveLineDiagonalBundleTensorTriangle

open Quillen

/-- The original standard ambient derived category, as used by the public triangle. -/
local instance standardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules :=
  HasDerivedCategory.standard _

/-- The first derived arrow is the original tensor incidence and the second the adjoint quotient. -/
theorem original_triangle_arrows (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    (diagonalBundleTensorTriangle R M).mor₁ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj M)).map
        (diagonalIncidence R)) ∧
    (diagonalBundleTensorTriangle R M).mor₂ = (singleFunctor (relativeSquare R).Modules 0).map
      ((moduleTensorLeftFunctor (relativeSquare R)
        ((Scheme.Modules.pullback (relativeFirst R)).obj M)).map
        (diagonalQuotientMap R)) := ⟨rfl, rfl⟩

/-- The middle component retains the original pulled-back coefficient arrow
and original quotient. -/
theorem original_coefficient_triangle_map (R : CommRingCat.{u})
    {M N : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] (f : M ⟶ N) :
    (diagonalBundleTensorTriangleMap R f).hom₂ =
      (singleFunctor (relativeSquare R).Modules 0).map
        ((moduleTensorCoefficientMap (relativeSquare R)
          ((Scheme.Modules.pullback (relativeFirst R)).map f)).app
          ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))) := rfl

/-- The actual connecting arrow is natural for the original coefficient triangle map. -/
theorem original_connecting_square (R : CommRingCat.{u})
    {M N : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] (f : M ⟶ N) :
    (diagonalBundleTensorTriangleMap R f).hom₃ ≫ (diagonalBundleTensorTriangle R N).mor₃ =
      (diagonalBundleTensorTriangle R M).mor₃ ≫
        (shiftFunctor (DerivedCategory (relativeSquare R).Modules) (1 : ℤ)).map
          (diagonalBundleTensorTriangleMap R f).hom₁ :=
  (diagonalBundleTensorTriangleMap R f).comm₃.symm

/-- The actual triangle maps preserve identity and composition of original coefficient arrows. -/
theorem original_triangle_functoriality (R : CommRingCat.{u})
    {M N P : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) M]
    [IsFiniteLocallyFree (twoChartLine R) N] [IsFiniteLocallyFree (twoChartLine R) P]
    (f : M ⟶ N) (g : N ⟶ P) :
    diagonalBundleTensorTriangleMap R (𝟙 M) = 𝟙 (diagonalBundleTensorTriangle R M) ∧
      diagonalBundleTensorTriangleMap R (f ≫ g) =
        diagonalBundleTensorTriangleMap R f ≫ diagonalBundleTensorTriangleMap R g :=
  ⟨diagonalBundleTensorTriangleMap_id R M, diagonalBundleTensorTriangleMap_comp R f g⟩

/-- General scheme coefficients use actual tensor kernel maps after local exactness. -/
def originalLocallyFreeTensorKernel {X : Scheme.{u}} (M : X.Modules)
    [IsFiniteLocallyFree X M] (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι (f := (moduleTensorLeftFunctor X M).map S.g)
      ((moduleTensorLeftFunctor X M).map S.f)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])) := by
  have h := tensor_shortExact_finiteLocallyFree M S hS
  have := h.mono_f
  exact h.exact.fIsKernel

/-- The actual tensor quotient remains a cokernel without supplying a chosen coefficient retract. -/
def originalTensorQuotient (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] :
    IsColimit (CokernelCofork.ofπ (diagonalBundleTensorSequence R M).g
      (diagonalBundleTensorSequence R M).zero) := by
  have h := diagonalBundleTensorSequence_shortExact R M
  have := h.epi_g
  exact h.exact.gIsCokernel

/-- The original negative line is now an allowed projective-line coefficient. -/
theorem negative_line_triangle (R : CommRingCat.{u}) :
    diagonalBundleTensorTriangle R (tautologicalLine R) ∈
      distTriang (DerivedCategory (relativeSquare R).Modules) :=
  diagonalBundleTensorTriangle_distinguished _ _

/-- The original quotient line is also an allowed coefficient. -/
theorem quotient_line_triangle (R : CommRingCat.{u}) :
    diagonalBundleTensorTriangle R (tautologicalQuotientLine R) ∈
      distTriang (DerivedCategory (relativeSquare R).Modules) :=
  diagonalBundleTensorTriangle_distinguished _ _

/-- The original negative line over a nonreduced ring retains its tensor triangle. -/
theorem nonreduced_original_triangle :
    diagonalBundleTensorTriangle (CommRingCat.of (ZMod 4))
      (tautologicalLine (CommRingCat.of (ZMod 4))) ∈
      distTriang (DerivedCategory (relativeSquare (CommRingCat.of (ZMod 4))).Modules) :=
  diagonalBundleTensorTriangle_distinguished _ _

/-- The same original tensor sequence is short exact over the zero ring. -/
theorem zeroRing_original_tensor_sequence :
    (diagonalBundleTensorSequence (CommRingCat.of (ZMod 1))
      (tautologicalQuotientLine (CommRingCat.of (ZMod 1)))).ShortExact :=
  diagonalBundleTensorSequence_shortExact _ _

end QuillenTest.ProjectiveLineDiagonalBundleTensorTriangle
