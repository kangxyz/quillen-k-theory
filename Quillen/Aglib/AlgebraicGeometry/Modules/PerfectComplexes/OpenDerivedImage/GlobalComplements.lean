/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalDensity
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Complements
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Global qcqs complements in the derived restriction image

For the original compact open immersion into a qcqs scheme, the actual global complement gives coproduct membership before any additional morphism-roof input.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Genuine global qcqs complement geometry supplies the original saturated
image complement, before imposing any derived morphism roof hypothesis. -/
theorem exists_global_perfect_complement (E : CochainComplex U.Modules ℤ)
    (hE : locallyPerfect U E) :
    ∃ C : CochainComplex U.Modules ℤ, locallyPerfect U C ∧ complexObjects j (C ⊞ E) := by
  obtain ⟨P, C, hP, hC, ⟨e⟩⟩ :=
    locallyPerfect_exists_global_perfect_complement_of_openImmersion j E hE
  exact ⟨C, hC, P, hP, ⟨e ≪≫ (DerivedCategory.Q (C := U.Modules)).mapIso (biprod.braiding E C)⟩⟩

/-- Actual chosen coproduct density for the original perfect category. -/
theorem global_complement [HasBinaryCoproducts (Perfect U)] (A : Perfect U) :
    ∃ B : Perfect U, objects j (A ⨿ B) := by
  obtain ⟨C, hC, hAC⟩ := exists_global_perfect_complement j A.obj A.property
  exact coprod_complement_of_complex_complement j A C hC hAC

end Quillen.PerfectComplexes.OpenDerivedImage

end

end
