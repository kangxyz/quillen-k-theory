/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.TwoChartStableCokernel

/-! Arbitrary signed degrees retain the original Laurent cone inclusion and signed loop shift. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.ConeStableCokernelDegree
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f)) (d : ℤ)
  [Subsingleton (stableHomotopyGroup E (d - 1))]

include hf in
/-- Every genuine cone class has an original target representative at the stated signed degree. -/
theorem original_representative (z : stableHomotopyGroup (mappingCone f) d) :
    ∃ x, (stableHomotopyFunctor d).map (mappingConeInclusion f) x = z :=
  stableMappingConeInclusion_degree_surjective f hf d z

/-- The categorical quotient retains the original cone inclusion. -/
theorem original_projection :
    cokernel.π ((stableHomotopyFunctor d).map f) ≫
      (stableMappingConeDegreeCokernelIso f hf d).hom =
    (stableHomotopyFunctor d).map (mappingConeInclusion f) :=
  stableMappingConeDegreeCokernelIso_π f hf d

end Quillen.Tests.ConeStableCokernelDegree
