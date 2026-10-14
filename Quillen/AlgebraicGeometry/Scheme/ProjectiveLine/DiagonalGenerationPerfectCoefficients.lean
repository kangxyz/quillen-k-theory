/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalPerfectGenerationRotation
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.IntrinsicPerfectPushforward

/-! # Intrinsic perfection of the actual G0/G1 generation coefficients

Use the accepted original derived projection producer, actual local line
trivializations and the installed original shift comparison. No natural
strictification or two-summand derived equivalence is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Pretriangulated AlgebraicGeometry
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.PerfectComplexes
local instance generationCoefficientsStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- The ORIGINAL G0(K)=Rp*K coefficient is intrinsically perfect over the actual base. -/
theorem perfect_diagonalGenerationG0 (K : OriginalPerfectPlus R) :
    perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj ((diagonalGenerationG0 R).obj K)) :=
  Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedProjection_of_perfect R K.obj K.property

/-- The ORIGINAL G1(K)=Rp*(K tensor L)[1] coefficient is intrinsically perfect over the base. -/
theorem perfect_diagonalGenerationG1 (K : OriginalPerfectPlus R) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj ((diagonalGenerationG1 R).obj K)) := by
  let Z := (derivedPushforwardPlus (projection R)).obj ((originalRightLineDerived R).obj K.obj)
  have hZ : perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj Z) :=
    Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedProjection_of_perfect R _
      (perfect_derivedTautologicalRightTensor R K.obj K.property)
  have hs := (perfectDerivedObjects (Spec R)).le_shift (1 : ℤ) _ hZ
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).app Z).symm hs
end Quillen.Scheme.ProjectiveLine
