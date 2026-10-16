/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalScalar
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RankOne
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections

/-!
# The original scalar on the structure single

The actual structure-sheaf unit multiplication is the same original scalar on the unchanged rank-one complex.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine
theorem unitMul_eq_globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    unitMul X r = (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app
      (SheafOfModules.unit X.ringCatSheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change x * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r =
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r * x
  exact mul_comm _ _

theorem single_unitMul_eq_globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (CochainComplex.singleFunctor X.Modules 0).map (unitMul X r) =
      (complexGlobalScalar X r).app (rankOnePerfect X).obj := by
  apply HomologicalComplex.from_single_hom_ext
  change ((HomologicalComplex.single X.Modules (.up ℤ) 0).map (unitMul X r)).f 0 =
    (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app
      (((HomologicalComplex.single X.Modules (.up ℤ) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)).X 0)
  rw [HomologicalComplex.single_map_f_self, unitMul_eq_globalScalar]
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit X.ringCatSheaf)
  change e.hom ≫ (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app _ ≫ e.inv =
    (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app _
  rw [← cancel_mono e.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ((AlgebraicGeometry.Scheme.Modules.globalScalar X r).naturality e.hom).symm


end Quillen.PerfectComplexes.ProjectiveLine
end
end
