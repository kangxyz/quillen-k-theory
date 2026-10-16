/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechSheafComplex
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleCech
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.StrictModuleModel

/-! # Actual strict-perfect models of vector-bundle sheaf Cech complexes

For every finite locally free sheaf on the original two-chart line over an
arbitrary commutative ring, the original signed sheaf Cech cone has an actual
strict-perfect homotopy model. Derived direct-image identification and arbitrary
perfect coefficients are separate obligations.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
/-- A finite locally free input has an actual strict-perfect homotopy model of its sheaf Cech
cone.
-/
theorem exists_strictSheafCech_model [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : StrictPerfect (Spec R),
      Nonempty (HomotopyEquiv (originalSheafCechComplex R M) P.obj) := by
  obtain ⟨P, hP, hfin, ⟨h⟩⟩ := exists_original_vectorBundle_cech_model R M
  have hstrict : Affine.moduleStrictPerfect R P := by
    refine ⟨⟨0, 1, fun i hi => hP i ?_ ?_⟩, hfin⟩ <;> omega
  let Q : StrictPerfect (Spec R) := ⟨(Affine.associatedComplex R).obj P,
    Affine.strictPerfect_associated R hstrict⟩
  exact ⟨Q, ⟨(HomotopyEquiv.ofIso (originalSheafCechSectionsIso R M).symm).trans
    ((tilde.functor R).mapHomotopyEquiv h)⟩⟩

end Quillen.PerfectComplexes.ProjectiveLine
end

end
