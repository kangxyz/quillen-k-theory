/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Cones of morphisms acyclic after open restriction

The original actual mapping cone is supported on the complement of the open whenever its restricted
chain map is a quasi-isomorphism.-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {K L : Perfect X} (f : K ⟶ L) (hf : QuasiIso ((restrict j).map f.hom))

include hf in
/-- The original mapping cone of an open-weak perfect morphism is genuinely supported. -/
theorem perfectOpenWeak_mappingCone_supported :
    perfectSupported j (CochainComplex.mappingCone f.hom) := by
  refine ⟨locallyPerfect_mappingCone K.property L.property f.hom, ?_⟩
  let : QuasiIso ((restrict j).map f.hom) :=
    hf
  intro n
  exact (CochainComplex.mappingCone_acyclic_of_quasiIso
    ((restrict j).map f.hom) n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f.hom
      (Scheme.Modules.restrictFunctor j)).symm

end Quillen.PerfectComplexes

end

end
