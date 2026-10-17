/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.QuotientTensor
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalSupportedTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine

/-!
# The actual derived diagonal term in the tensor triangle

The original diagonal is closed, hence affine. The actual tensor of a vector
bundle with the quotient line is finite locally free and quasicoherent. Thus
the installed bounded-below derived direct-image unit is invertible on this
single sheaf. Transport the original diagonal-supported tensor triangle
through that actual unit, retaining its arrows and connecting morphism.
This gives a genuine derived diagonal term; it does not assert generation.
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
/-- Standard original derived categories for both geometric schemes. -/
local instance diagonalDerivedTensorStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
  [IsFiniteLocallyFree (twoChartLine R) E]
/-- The actual installed diagonal derived unit is invertible on the original tensor sheaf. -/
instance isIso_diagonalDerivedUnit_quotientTensor :
    IsIso ((derivedPushforwardPlusUnit (relativeDiagonal R)).app
      (singleZeroPlus (twoChartLine R)
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)))) :=
  by
    let : IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R
    exact isIso_derivedPushforwardPlusUnit_single (relativeDiagonal R) _
/-- The actual ordinary diagonal direct image is compared with its installed derived image. -/
def diagonalQuotientTensorDerivedIso :
    DerivedCategory.Plus.Q.obj (singleZeroPlus (relativeSquare R)
      ((Scheme.Modules.pushforward (relativeDiagonal R)).obj
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)))) ≅
    (derivedPushforwardPlus (relativeDiagonal R)).obj
      (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R)
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R)))) :=
  (DerivedCategory.Plus.Q.mapIso (pushforwardSingleZeroPlusIso (relativeDiagonal R) _)).symm ≪≫
    asIso ((derivedPushforwardPlusUnit (relativeDiagonal R)).app _)
/-- The comparison uses exactly the installed derived unit after the original single comparison. -/
theorem diagonalQuotientTensorDerivedIso_hom :
    (diagonalQuotientTensorDerivedIso R E).hom =
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso (relativeDiagonal R) _).inv ≫
        (derivedPushforwardPlusUnit (relativeDiagonal R)).app
          (singleZeroPlus (twoChartLine R)
            ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))) := rfl
/-- The actual third vertex is the original bounded-below derived diagonal image
in the ambient category. -/
def diagonalSupportedDerivedVertexIso :
    (diagonalSupportedTensorTriangle R E).obj₃ ≅
      DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (relativeDiagonal R)).obj
        (DerivedCategory.Plus.Q.obj (singleZeroPlus (twoChartLine R)
          ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))))) :=
  (singleFunctorIsoCompQ (relativeSquare R).Modules 0).app _ ≪≫
    ((DerivedCategory.Plus.QCompιIso (relativeSquare R).Modules).app
      (singleZeroPlus (relativeSquare R) _)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (diagonalQuotientTensorDerivedIso R E)
/-- The original tensor triangle with the actual derived diagonal direct-image term. -/
def diagonalDerivedTensorTriangle : Triangle (DerivedCategory (relativeSquare R).Modules) :=
  Triangle.mk (diagonalSupportedTensorTriangle R E).mor₁
    ((diagonalSupportedTensorTriangle R E).mor₂ ≫ (diagonalSupportedDerivedVertexIso R E).hom)
    ((diagonalSupportedDerivedVertexIso R E).inv ≫ (diagonalSupportedTensorTriangle R E).mor₃)
/-- The two original arrows and connecting map are transported through the actual derived unit. -/
def diagonalDerivedTensorTriangleIso :
    diagonalDerivedTensorTriangle R E ≅ diagonalSupportedTensorTriangle R E := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (diagonalSupportedDerivedVertexIso R E).symm ?_ ?_ ?_
  all_goals dsimp [diagonalDerivedTensorTriangle]; simp
/-- The triangle with the genuine derived diagonal image is distinguished. -/
theorem diagonalDerivedTensorTriangle_distinguished :
    diagonalDerivedTensorTriangle R E ∈ distTriang (DerivedCategory (relativeSquare R).Modules) :=
  isomorphic_distinguished _ (diagonalSupportedTensorTriangle_distinguished R E) _
    (diagonalDerivedTensorTriangleIso R E)
end AlgebraicGeometry.Scheme.ProjectiveLine
