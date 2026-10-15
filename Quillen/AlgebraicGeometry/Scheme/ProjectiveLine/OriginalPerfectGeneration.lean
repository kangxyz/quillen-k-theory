/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationPerfectCoefficients
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationUnitEquations
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationSingle

/-! # Actual original two-line generation of intrinsic perfect D+

The natural distinguished triangle with actual perfect G0/G1 coefficients
proves generation by the original flat pullback and its original left-L tensor.
No equivalence with two summands and no K-theory inverse is inferred.
-/
@[expose] public section

open Quillen.PerfectComplexes

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance originalGenerationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- Any isomorphism-stable triangulated extension class containing the ORIGINAL
pullback of base perfect objects and its ORIGINAL left-L tensor contains every
intrinsic perfect D+ object on the actual projective line. -/
theorem originalPerfectPlus_generation
    (P : ObjectProperty (DerivedCategory.Plus (twoChartLine R).Modules))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂]
    (h₀ : ∀ A : DerivedCategory.Plus (Spec R).Modules,
      perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj A) →
        P ((derivedFlatPullbackPlus (projection R)).obj A))
    (h₁ : ∀ A : DerivedCategory.Plus (Spec R).Modules,
      perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj A) →
        P ((originalLeftLineDerived R).obj ((derivedFlatPullbackPlus (projection R)).obj A)))
    (K : OriginalPerfectPlus R) : P K.obj := by
  apply P.ext_of_isTriangulatedClosed₂ (diagonalRotatedGenerationTriangle R K)
    (diagonalRotatedGenerationTriangle_distinguished R K)
  · exact h₀ ((diagonalGenerationG0 R).obj K) (perfect_diagonalGenerationG0 R K)
  · exact h₁ ((diagonalGenerationG1 R).obj K) (perfect_diagonalGenerationG1 R K)
end AlgebraicGeometry.Scheme.ProjectiveLine
