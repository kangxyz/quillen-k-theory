/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineCoordinateChart
public import QuillenTest.LineCoordinateTensor

/-! The original scalar chart comparison retains arbitrary coefficient complexes. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.Modules
namespace QuillenTest.LineCoordinateChart

/-- Cancelling the actual chart isomorphism leaves the exact original scalar map. -/
theorem original_chart_inverse_scalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) (r : Γ(U, ⊤))
    (h : (Scheme.Modules.restrictFunctor j).map f ≫
      (Scheme.Modules.restrictUnitIso j).hom = e.hom ≫ unitMul U r)
        (K : CochainComplex X.Modules ℤ) :
    (tensorByLineComplexChartIso j L e).inv.app K ≫
        (restrict j).map ((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K) =
      (complexGlobalScalar U r).app ((restrict j).obj K) := by
  rw [complexLineCoordinate_chart_scalar j f e r h K]
  simp

end QuillenTest.LineCoordinateChart
