/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Actual cone closure for supported perfect complexes

The literal mapping cone of a map between existing supported perfect
complexes has the same support. Exact original restriction identifies its
cone with the cone of a map between acyclic complexes. This foundational
closure theorem has no geometric roof or density dependency.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes

/-- The literal cone of a supported morphism remains supported. -/
lemma perfectSupported_mappingCone {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : CochainComplex X.Modules ℤ} (hK : perfectSupported j K) (hL : perfectSupported j L)
      (f : K ⟶ L) :
    perfectSupported j (CochainComplex.mappingCone f) := by
  refine ⟨locallyPerfect_mappingCone hK.1 hL.1 f, ?_⟩
  have : QuasiIso ((restrict j).map f) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n (hK.2 n)).mpr (hL.2 n)
  have hc := CochainComplex.mappingCone_acyclic_of_quasiIso ((restrict j).map f)
  intro n
  exact (hc n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor j)).symm

end Quillen.PerfectComplexes
