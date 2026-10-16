/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineCoordinateTensor

/-! Named consumers of the original tensor coordinate, scalar and restriction maps. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.Modules
namespace QuillenTest.LineCoordinateTensor

/-- Original restriction retains the exact coefficient arrow and structure comparison. -/
theorem original_restriction_square {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).map ((AlgebraicGeometry.Scheme.Modules.tensorToUnit f).app M)
      =
      (tensorRestrictionIso j L M).inv ≫
        (AlgebraicGeometry.Scheme.Modules.tensorToUnit ((Scheme.Modules.restrictFunctor j).map f ≫
          (Scheme.Modules.restrictUnitIso j).hom)).app (M.restrict j) :=
  (tensorRestrictionIso j L M).eq_inv_comp.mpr
    (AlgebraicGeometry.Scheme.Modules.tensorToUnit_restrict j f M)

/-- Original unit multiplication acts on arbitrary coefficient modules. -/
theorem original_unit_scalar (X : Scheme.{u}) (r : Γ(X, ⊤)) (M : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.tensorToUnit (unitMul X r)).app M =
      (tensorLeftUnitIso X.sheaf).hom.app M ≫ (globalScalar X r).app M :=
  NatTrans.congr_app (moduleLineCoordinate_unitMul X r) M

/-- Degreewise original coordinates are natural on arbitrary coefficient chain maps. -/
theorem original_coordinate_naturality {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) {K M : CochainComplex X.Modules ℤ} (g : K ⟶ M) :
    (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L).map g ≫
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app M =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K ≫ g :=
  (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).naturality g

end QuillenTest.LineCoordinateTensor
