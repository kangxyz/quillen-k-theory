/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalBundleTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalTensorPushforward

/-!
# The diagonal-supported term of the actual tensor triangle

Identify the third term of the original twisted diagonal tensor triangle with
the original diagonal pushforward of the tensor with the quotient line.
The incidence arrow is unchanged; the quotient arrow and connecting morphism
are transported through the actual diagonal projection-formula isomorphism.
This is an ordinary sheaf direct image placed in degree zero. Derived direct
image and projective-bundle generation require further comparison.
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

/-- The standard derived category used for the original relative square. -/
local instance diagonalSupportedTensorStandardDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (relativeSquare R).Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
  [IsFiniteLocallyFree (twoChartLine R) E]

/-- Place the actual diagonal tensor comparison in degree zero. -/
def diagonalTensorSingleIso :
    (diagonalBundleTensorTriangle R E).obj₃ ≅
      (singleFunctor (relativeSquare R).Modules 0).obj
        ((Scheme.Modules.pushforward (relativeDiagonal R)).obj
          ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalQuotientLine R))) :=
  (singleFunctor (relativeSquare R).Modules 0).mapIso
    (diagonalTensorPushforwardIso R E (tautologicalQuotientLine R))

/-- The original tensor triangle with its actual diagonal-supported third vertex. -/
def diagonalSupportedTensorTriangle : Triangle (DerivedCategory (relativeSquare R).Modules) :=
  Triangle.mk (diagonalBundleTensorTriangle R E).mor₁
    ((diagonalBundleTensorTriangle R E).mor₂ ≫ (diagonalTensorSingleIso R E).hom)
    ((diagonalTensorSingleIso R E).inv ≫ (diagonalBundleTensorTriangle R E).mor₃)

/-- The identification retains both identity components and the original diagonal comparison. -/
def diagonalSupportedTensorTriangleIso :
    diagonalSupportedTensorTriangle R E ≅ diagonalBundleTensorTriangle R E := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (diagonalTensorSingleIso R E).symm ?_ ?_ ?_
  all_goals dsimp [diagonalSupportedTensorTriangle]; simp

/-- The triangle with the original diagonal-supported term is genuinely distinguished. -/
theorem diagonalSupportedTensorTriangle_distinguished :
    diagonalSupportedTensorTriangle R E ∈ distTriang (DerivedCategory (relativeSquare R).Modules) :=
  isomorphic_distinguished _ (diagonalBundleTensorTriangle_distinguished R E) _
    (diagonalSupportedTensorTriangleIso R E)

/-- The incidence arrow is still the original tensor incidence, placed in degree zero. -/
theorem diagonalSupportedTensorTriangle_mor₁ :
    (diagonalSupportedTensorTriangle R E).mor₁ =
      (singleFunctor (relativeSquare R).Modules 0).map
        ((moduleTensorLeftFunctor (relativeSquare R)
          ((Scheme.Modules.pullback (relativeFirst R)).obj E)).map (diagonalIncidence R)) := rfl

/-- The quotient arrow retains the literal tensor quotient followed by the actual comparison. -/
theorem diagonalSupportedTensorTriangle_mor₂ :
    (diagonalSupportedTensorTriangle R E).mor₂ =
      (singleFunctor (relativeSquare R).Modules 0).map
        ((moduleTensorLeftFunctor (relativeSquare R)
          ((Scheme.Modules.pullback (relativeFirst R)).obj E)).map (diagonalQuotientMap R)) ≫
      (singleFunctor (relativeSquare R).Modules 0).map
        (projectionFormulaMap (relativeDiagonal R)
          ((Scheme.Modules.pullback (relativeFirst R)).obj E) (tautologicalQuotientLine R) ≫
        (Scheme.Modules.pushforward (relativeDiagonal R)).map
          ((moduleTensorCoefficientMap (twoChartLine R)
            ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
              (relativeDiagonal_first R)).hom.app E)).app (tautologicalQuotientLine R))) := rfl

/-- The connecting morphism is the original connecting map after the actual inverse comparison. -/
theorem diagonalSupportedTensorTriangle_mor₃ :
    (diagonalSupportedTensorTriangle R E).mor₃ =
      (singleFunctor (relativeSquare R).Modules 0).map
        (diagonalTensorPushforwardIso R E (tautologicalQuotientLine R)).inv ≫
        (diagonalBundleTensorTriangle R E).mor₃ := rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
