/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitAction

/-!
# Original unit-single components of the tensor action

The coefficient tensor automorphism followed by the genuine unitor is the original tensor-to-unit
map. On the actual single complex of the structure module, this is the original single map of
the global-unit automorphism. In particular, degree zero retains the specified pair `(O[0], μr)`.

Intended upstream owner:
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitSingle`.
The hypotheses are an arbitrary scheme and a global unit. The current consumer is the restricted
tensor-unit action comparison in Quillen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
universe u
namespace Quillen.PerfectComplexes

/-- The coefficient tensor action followed by the unitor is the original tensor-to-unit map. -/
theorem complexTensorUnitAutomorphism_toUnit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom =
      AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit (unitMul X r) := by
  apply NatTrans.ext
  funext K
  ext n : 1
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    complexTensorUnitAutomorphism_hom_f, complexTensorUnitIso_hom_f,
    AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_f]
  rfl

/-- The unit-single component is the actual single map of the structure-module automorphism. -/
theorem complexTensorUnitAutomorphism_single (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (n : ℤ) :
    ((complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom).app
        ((CochainComplex.singleFunctor X.Modules n).obj (SheafOfModules.unit X.ringCatSheaf)) =
      (tensorLeftSingleUnitIso X (SheafOfModules.unit X.ringCatSheaf) n).hom ≫
        (CochainComplex.singleFunctor X.Modules n).map (unitMul X r) := by
  rw [complexTensorUnitAutomorphism_toUnit]
  exact AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_single (unitMul X r) n

end Quillen.PerfectComplexes
