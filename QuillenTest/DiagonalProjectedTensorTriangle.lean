/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalProjectedTensorTriangle

/-!
# Consumers of the original projected diagonal triangle

Inspect the installed units, actual short-exact connecting arrow, original
second-projection maps, and coefficient identification over arbitrary rings.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory AlgebraicGeometry CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace QuillenTest.DiagonalProjectedTensorTriangle

open Quillen

/-- Standard original module-sheaf derived categories for the consumers. -/
local instance projectedConsumerStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The installed derived identity unit is recovered from its canonical comparison. -/
theorem original_identity_unit (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughInjectives C] [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.Q.map ((Functor.mapCochainComplexPlusIdIso C).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusIdIso C).inv.app (DerivedCategory.Plus.Q.obj K) =
        (𝟭 C).rightDerivedFunctorPlusUnit.app K := by
  rw [← Functor.rightDerivedFunctorPlusIdIso_unit]
  simp

/-- Forgetting the bound retains the actual original short-exact connecting arrow. -/
theorem original_single_connecting (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory C] (S : ShortComplex C) (hS : S.ShortExact) :
    DerivedCategory.Plus.ι.map hS.singleTrianglePlus.mor₃ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ := by
  change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) ≫ _ = _
  rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id hS.singleδ

/-- Both original installed units appear in the diagonal section comparison. -/
theorem original_diagonal_units (R : CommRingCat.{u})
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (derivedPushforwardPlusUnit (relativeSecond R)).app
        ((Scheme.Modules.pushforward (relativeDiagonal R)).mapCochainComplexPlus.obj K) ≫
      (derivedPushforwardPlus (relativeSecond R)).map
        ((derivedPushforwardPlusUnit (relativeDiagonal R)).app K) ≫
      (derivedDiagonalSecondIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (sectionPushforwardIso
          (relativeDiagonal R) (relativeSecond R) (relativeDiagonal_second R))).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (twoChartLine R).Modules).hom.app K) := by
  have h := derivedDiagonalSecondIso_unit R K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at h
  exact h

/-- The diagonal section comparison is natural on arbitrary original derived arrows. -/
theorem original_diagonal_naturality (R : CommRingCat.{u})
    {K L : DerivedCategory.Plus (twoChartLine R).Modules} (f : K ⟶ L) :
    (derivedPushforwardPlus (relativeSecond R)).map
        ((derivedPushforwardPlus (relativeDiagonal R)).map f) ≫
      (derivedDiagonalSecondIso R).hom.app L =
        (derivedDiagonalSecondIso R).hom.app K ≫ f :=
  (derivedDiagonalSecondIso R).hom.naturality f

variable (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
  [IsFiniteLocallyFree (twoChartLine R) E]

/-- The first arrow is literally the original derived image of the incidence arrow. -/
theorem original_projected_incidence :
    (diagonalCoefficientTensorTriangle R E).mor₁ =
      (derivedPushforwardPlus (relativeSecond R)).map
        ((diagonalBundleTensorTrianglePlus R E).mor₁) := rfl

/-- The coefficient quotient arrow recovers the actual projected quotient arrow. -/
theorem original_projected_quotient :
    (diagonalCoefficientTensorTriangle R E).mor₂ ≫
      (diagonalProjectedTensorVertexIso R E).inv =
        (diagonalProjectedTensorTriangle R E).mor₂ := by
  change (_ ≫ _) ≫ _ = _
  simp

/-- The connecting arrow retains the installed shift comparison of the original Rp₂. -/
theorem original_projected_connecting :
    (diagonalProjectedTensorVertexIso R E).hom ≫
      (diagonalCoefficientTensorTriangle R E).mor₃ =
        (derivedPushforwardPlus (relativeSecond R)).map
          ((diagonalDerivedTensorTrianglePlus R E).mor₃) ≫
        ((derivedPushforwardPlus (relativeSecond R)).commShiftIso (1 : ℤ)).hom.app
          (diagonalDerivedTensorTrianglePlus R E).obj₁ := by
  change _ ≫ (_ ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The actual distinguished coefficient triangle exists over a nonreduced base. -/
theorem nonreduced_distinguished
    (E : (twoChartLine (CommRingCat.of (ZMod 4))).Modules)
    [IsFiniteLocallyFree (twoChartLine (CommRingCat.of (ZMod 4))) E] :
    diagonalCoefficientTensorTriangle (CommRingCat.of (ZMod 4)) E ∈
      distTriang (DerivedCategory.Plus (twoChartLine (CommRingCat.of (ZMod 4))).Modules) :=
  diagonalCoefficientTensorTriangle_distinguished _ E

/-- The original construction remains distinguished over the zero ring. -/
theorem zero_ring_distinguished
    (E : (twoChartLine (CommRingCat.of (ZMod 1))).Modules)
    [IsFiniteLocallyFree (twoChartLine (CommRingCat.of (ZMod 1))) E] :
    diagonalCoefficientTensorTriangle (CommRingCat.of (ZMod 1)) E ∈
      distTriang (DerivedCategory.Plus (twoChartLine (CommRingCat.of (ZMod 1))).Modules) :=
  diagonalCoefficientTensorTriangle_distinguished _ E

end QuillenTest.DiagonalProjectedTensorTriangle
