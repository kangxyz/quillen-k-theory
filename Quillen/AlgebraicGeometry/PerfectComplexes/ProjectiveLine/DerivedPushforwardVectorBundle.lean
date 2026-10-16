/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedCechCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.CechModel
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-! # Perfect derived direct images of projective-line vector bundles

The original derived direct image of a finite locally free sheaf on the genuine two-chart
line has an actual strict-perfect representative over the arbitrary base ring. The proof
uses the original derived Cech comparison and the proved finite-projective Cech model.
Arbitrary locally perfect coefficients and projective generation are separate obligations. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine
/-- The standard ambient derived category of original module sheaves. -/
local instance derivedCechPerfectStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- Transport an actual sheaf Cech homotopy model through the original derived comparison. -/
def derivedCechStrictModelIso [M.IsQuasicoherent] (P : StrictPerfect (Spec R))
    (h : HomotopyEquiv (originalSheafCechComplex R M) P.obj) :
    DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
      DerivedCategory.Q.obj P.obj := by
  have : QuasiIso h.hom := h.quasiIso_hom
  exact derivedCechConeIso R M ≪≫ asIso (DerivedCategory.Q.map h.hom)

variable [IsFiniteLocallyFree (twoChartLine R) M]

/-- An actual finite locally free sheaf has a strict-perfect original derived direct image. -/
theorem exists_derivedPushforward_vectorBundle_strict_model :
    ∃ P : StrictPerfect (Spec R),
      Nonempty (DerivedCategory.Plus.ι.obj
          ((derivedPushforwardPlus (projection R)).obj
            ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
        DerivedCategory.Q.obj P.obj) := by
  obtain ⟨P, ⟨h⟩⟩ := exists_strictSheafCech_model R M
  exact ⟨P, ⟨derivedCechStrictModelIso R M P h⟩⟩

/-- The original derived direct image of a vector bundle is intrinsically perfect. -/
theorem perfect_derivedPushforward_vectorBundle :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M))) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_derivedPushforward_vectorBundle_strict_model R M
  exact (perfectDerivedObjects (Spec R)).prop_of_iso e.symm
    ((perfectDerivedObjects_toDerived_iff (Spec R) P.obj).mpr
      (locallyPerfect_of_strictPerfect P.property))
end Quillen.PerfectComplexes.ProjectiveLine
