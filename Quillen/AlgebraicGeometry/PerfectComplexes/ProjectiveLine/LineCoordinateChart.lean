/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineCoordinateTensor

/-!
# Original coordinate scalars in the original line-tensor chart

The specified line chart identifies the literal restricted coordinate with the original scalar
on every coefficient complex. All tensor, restriction and unit comparisons are the existing ones.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Modules

/-- Precomposing the coordinate uses the original coefficient tensor map. -/
theorem moduleLineCoordinate_comp {X : Scheme.{u}} {L M : X.Modules}
    (g : L ⟶ M) (f : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.Modules.tensorToUnit (g ≫ f) =
      moduleTensorCoefficientMap X g ≫ AlgebraicGeometry.Scheme.Modules.tensorToUnit f := by
  rw [AlgebraicGeometry.Scheme.Modules.tensorToUnit, moduleTensorCoefficientMap_comp,
    Category.assoc]
  rfl

/-- A coordinate equal to the specified trivialization gives that same tensor chart map. -/
theorem moduleLineCoordinate_chart_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor j).map f ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).map ((AlgebraicGeometry.Scheme.Modules.tensorToUnit f).app M)
      =
      (tensorByLineModuleChartIso j L e).hom.app M := by
  rw [(tensorRestrictionIso j L M).eq_inv_comp.mpr
    (AlgebraicGeometry.Scheme.Modules.tensorToUnit_restrict j f M), h]
  simp [tensorByLineModuleChartIso, AlgebraicGeometry.Scheme.Modules.tensorToUnit,
    moduleTensorCoefficientMap,
    tensorRestrictionNatIso]

/-- The literal restricted coordinate is the original chart trivialization then scalar. -/
theorem moduleLineCoordinate_chart_scalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) (r : Γ(U, ⊤))
    (h : (Scheme.Modules.restrictFunctor j).map f ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom ≫ unitMul U r) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).map ((AlgebraicGeometry.Scheme.Modules.tensorToUnit f).app M)
      =
      (tensorByLineModuleChartIso j L e).hom.app M ≫
        (globalScalar U r).app (M.restrict j) := by
  rw [(tensorRestrictionIso j L M).eq_inv_comp.mpr
    (AlgebraicGeometry.Scheme.Modules.tensorToUnit_restrict j f M), h, moduleLineCoordinate_comp,
    moduleLineCoordinate_unitMul]
  simp [tensorByLineModuleChartIso, moduleTensorCoefficientMap, tensorRestrictionNatIso,
    Category.assoc]

/-- The same original chart isomorphism identifies the positive coordinate on every complex. -/
theorem complexLineCoordinate_chart_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf)
    (h : (Scheme.Modules.restrictFunctor j).map f ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom) (K : CochainComplex X.Modules ℤ) :
    (restrict j).map ((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K) =
      (tensorByLineComplexChartIso j L e).hom.app K := by
  ext n : 1
  change (Scheme.Modules.restrictFunctor j).map
    (((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K).f n) =
      (tensorByLineModuleChartIso j L e).hom.app (K.X n)
  rw [AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_f]
  exact moduleLineCoordinate_chart_iso j f e h (K.X n)

/-- The original line-tensor chart formula holds degreewise on arbitrary complexes. -/
theorem complexLineCoordinate_chart_scalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) (r : Γ(U, ⊤))
    (h : (Scheme.Modules.restrictFunctor j).map f ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom ≫ unitMul U r)
        (K : CochainComplex X.Modules ℤ) :
    (restrict j).map ((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K) =
      (tensorByLineComplexChartIso j L e).hom.app K ≫
        (complexGlobalScalar U r).app ((restrict j).obj K) := by
  ext n : 1
  change (Scheme.Modules.restrictFunctor j).map
    (((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K).f n) =
      (tensorByLineModuleChartIso j L e).hom.app (K.X n) ≫
        (globalScalar U r).app ((K.X n).restrict j)
  rw [AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_f]
  exact moduleLineCoordinate_chart_scalar j f e r h (K.X n)

end Quillen.PerfectComplexes
