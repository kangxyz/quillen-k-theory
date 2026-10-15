/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardSection
public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalDerivedTensorTriangle
/-!
# The original diagonal triangle after derived second projection

For a vector bundle on the genuine two-chart projective line, apply the actual
bounded-below derived second projection to the original tensor diagonal triangle.
The original diagonal section equality identifies its third term with the single
of the coefficient tensored with the quotient line. The incidence and connecting
arrows are retained. The first two terms remain actual derived-image objects;
no generation or projective-bundle equivalence is asserted. All base rings,
including the zero ring, are allowed.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry DerivedCategory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- Standard original module-sheaf derived categories. -/
local instance projectedTensorStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The original diagonal and second projection give the canonical derived identity. -/
def derivedDiagonalSecondIso (R : CommRingCat.{u}) :
    derivedPushforwardPlus (relativeDiagonal R) ⋙ derivedPushforwardPlus (relativeSecond R) ≅
      𝟭 (DerivedCategory.Plus (twoChartLine R).Modules) :=
  derivedPushforwardPlusSectionIso (relativeDiagonal R) (relativeSecond R)
    (relativeDiagonal_second R)
/-- This diagonal identity retains its original geometric section equality and installed units. -/
theorem derivedDiagonalSecondIso_unit (R : CommRingCat.{u})
    (K : CochainComplex.Plus (twoChartLine R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward (relativeDiagonal R))
      (Scheme.Modules.pushforward (relativeSecond R))).app K ≫
        (derivedDiagonalSecondIso R).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (sectionPushforwardIso
          (relativeDiagonal R) (relativeSecond R) (relativeDiagonal_second R))).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (twoChartLine R).Modules).hom.app K) :=
  derivedPushforwardPlusSectionIso_unit _ _ _ K
variable (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
  [IsFiniteLocallyFree (twoChartLine R) E]
/-- The original short-exact tensor triangle inside the actual bounded-below derived category. -/
def diagonalBundleTensorTrianglePlus :
    Triangle (DerivedCategory.Plus (relativeSquare R).Modules) :=
  (diagonalBundleTensorSequence_shortExact R E).singleTrianglePlus
/-- The actual third-vertex identification, lifted through the original fully faithful inclusion. -/
def diagonalTensorDerivedPlusIso :
    (diagonalBundleTensorTrianglePlus R E).obj₃ ≅
      (derivedPushforwardPlus (relativeDiagonal R)).obj
        (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R)
          ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)))) :=
  DerivedCategory.Plus.ι.preimageIso
    (diagonalTensorSingleIso R E ≪≫ diagonalSupportedDerivedVertexIso R E)
/-- The bounded-below original tensor triangle with its genuine derived diagonal term. -/
def diagonalDerivedTensorTrianglePlus :
    Triangle (DerivedCategory.Plus (relativeSquare R).Modules) :=
  Triangle.mk (diagonalBundleTensorTrianglePlus R E).mor₁
    ((diagonalBundleTensorTrianglePlus R E).mor₂ ≫ (diagonalTensorDerivedPlusIso R E).hom)
    ((diagonalTensorDerivedPlusIso R E).inv ≫ (diagonalBundleTensorTrianglePlus R E).mor₃)
/-- The actual diagonal comparison retains the two original incidence endpoints. -/
def diagonalDerivedTensorTrianglePlusIso :
    diagonalDerivedTensorTrianglePlus R E ≅ diagonalBundleTensorTrianglePlus R E := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (diagonalTensorDerivedPlusIso R E).symm ?_ ?_ ?_
  all_goals dsimp [diagonalDerivedTensorTrianglePlus]; simp
/-- The actual bounded-below triangle is distinguished. -/
theorem diagonalDerivedTensorTrianglePlus_distinguished :
    diagonalDerivedTensorTrianglePlus R E ∈
      distTriang (DerivedCategory.Plus (relativeSquare R).Modules) :=
  isomorphic_distinguished _
    (diagonalBundleTensorSequence_shortExact R E).singleTrianglePlus_distinguished _
    (diagonalDerivedTensorTrianglePlusIso R E)
/-- Apply the original second-projection derived direct image to the actual diagonal triangle. -/
def diagonalProjectedTensorTriangle :
    Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  (derivedPushforwardPlus (relativeSecond R)).mapTriangle.obj
    (diagonalDerivedTensorTrianglePlus R E)
/-- The actual derived direct image of the diagonal triangle is distinguished. -/
theorem diagonalProjectedTensorTriangle_distinguished :
    diagonalProjectedTensorTriangle R E ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  (derivedPushforwardPlus (relativeSecond R)).map_distinguished _
    (diagonalDerivedTensorTrianglePlus_distinguished R E)
/-- The actual geometric section comparison identifies the projected third vertex. -/
def diagonalProjectedTensorVertexIso :
    (diagonalProjectedTensorTriangle R E).obj₃ ≅
      DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R)
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))) :=
  (derivedDiagonalSecondIso R).app _
/-- The original projected diagonal triangle with its identified coefficient term. -/
def diagonalCoefficientTensorTriangle :
    Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  Triangle.mk (diagonalProjectedTensorTriangle R E).mor₁
    ((diagonalProjectedTensorTriangle R E).mor₂ ≫ (diagonalProjectedTensorVertexIso R E).hom)
    ((diagonalProjectedTensorVertexIso R E).inv ≫ (diagonalProjectedTensorTriangle R E).mor₃)
/-- The coefficient identification preserves the original projected triangle. -/
def diagonalCoefficientTensorTriangleIso :
    diagonalCoefficientTensorTriangle R E ≅ diagonalProjectedTensorTriangle R E := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (diagonalProjectedTensorVertexIso R E).symm ?_ ?_ ?_
  all_goals dsimp [diagonalCoefficientTensorTriangle]; simp
/-- The coefficient triangle is genuinely distinguished, with original derived-image terms. -/
theorem diagonalCoefficientTensorTriangle_distinguished :
    diagonalCoefficientTensorTriangle R E ∈
      distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  isomorphic_distinguished _ (diagonalProjectedTensorTriangle_distinguished R E) _
    (diagonalCoefficientTensorTriangleIso R E)
end AlgebraicGeometry.Scheme.ProjectiveLine
