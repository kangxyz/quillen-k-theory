/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Open restriction and the original cohomological bound

Exact original open restriction preserves the stated upper cohomological bound.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Complex AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
theorem restrict_isLE {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsLE b] :
    ((restrict j).obj K).IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact (K.exactAt_of_isLE b i hi).map (Scheme.Modules.restrictFunctor j)


end Quillen.PerfectComplexes.ProjectiveLine
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Complex AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
theorem restriction_isLE {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsLE b] :
    ((restrict j).obj K).IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact (K.exactAt_of_isLE b i hi).map (Scheme.Modules.restrictFunctor j)


end Quillen.PerfectComplexes.ProjectiveLine
end
end
