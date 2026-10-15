/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalDensity
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Dense

/-!
# Genuine global qcqs density in the original derived image

The global perfect-complement theorem supplies actual coproduct density for
the derived-saturated image of any original compact open immersion into a
qcqs scheme. Together with original morphism roofs this gives the standard
DenseCofiberData, including genuine extension and quotient closure in the
unchanged perfect-complex category. The complement itself uses no roof premise.
-/
@[expose] public section

open Quillen.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Genuine global qcqs complement geometry supplies the original saturated
image complement, before imposing any derived morphism roof hypothesis. -/
theorem exists_global_perfect_complement (E : Complex U) (hE : locallyPerfect U E) :
    ∃ C : Complex U, locallyPerfect U C ∧ complexObjects j (C ⊞ E) := by
  obtain ⟨P, C, hP, hC, ⟨e⟩⟩ :=
    locallyPerfect_exists_global_perfect_complement_of_openImmersion j E hE
  exact ⟨C, hC, P, hP, ⟨e ≪≫ (toDerived U).mapIso (biprod.braiding E C)⟩⟩

/-- Actual chosen coproduct density for the original perfect category. -/
theorem global_complement [HasBinaryCoproducts (Perfect U)] (A : Perfect U) :
    ∃ B : Perfect U, objects j (A ⨿ B) := by
  obtain ⟨C, hC, hAC⟩ := exists_global_perfect_complement j A.obj A.property
  exact coprod_complement_of_complex_complement j A C hC hAC

/-- Genuine qcqs density and closure reduce cofinality precisely to original
morphism roofs; no complement or joint-data hypothesis remains. -/
theorem globalDenseData (hroof : HasDerivedRoofs j) [HasBinaryCoproducts (Perfect U)] :
    Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j) where
  zero := zero_mem j
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso j f.hom
  extension := extension_mem j hroof
  quotient := quotient_mem j hroof
  complement := global_complement j

end Quillen.PerfectComplexes.OpenDerivedImage
