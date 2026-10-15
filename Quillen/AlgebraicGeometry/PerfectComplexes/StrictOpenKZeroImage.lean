/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.StrictOpenRelative
public import Quillen.Waldhausen.Fibration.ComplexExtension
public import Quillen.Waldhausen.Fibration.GeneralComparison
public import Quillen.Waldhausen.Fibration.LongExactSequence

/-! # The exact original strict relative K-zero image

The original cone cylinder and actual inverse-image extension axiom prove the
strict relative fibration. Its genuine degree-zero tail identifies the image
of relative restriction with that of the unchanged original strict restriction.
No full-target K-zero surjectivity is inferred.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.StrictOpenWeakImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual restriction and cofiber extension prove the genuine relative extension axiom. -/
theorem coarse_extensionAxiom : ExtensionAxiom (coarseWaldhausen j) :=
  Structure.withInverseImageWeak_extensionAxiom (strictRestrict_waldhausenExact j)
    (complexSubcategory_extensionAxiom (strictPerfect U))

/-- The original relative joint cylinder has its genuine second-endpoint section. -/
theorem jointData_section : RowFactorization.SecondEndpointSection (nested j) (jointData j) :=
  complexJointDataOfNested_secondEndpointSection (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)
    (fun _ hK ↦ strictPerfect_shift hK 1) (nested j)

/-- The actual original strict relative fiber comparison is a complete weak equivalence. -/
theorem canonicalFiberMap_weak : IsWeakHomotopyEquivalence (canonicalFiberMap (nested j)) := by
  let : (nested j).coarse.weq.HasTwoOutOfThreeProperty := coarse_twoOutOfThree j
  exact canonicalFiberMap_isWeakHomotopyEquivalence_general (nested j)
    (coarse_extensionAxiom j) (jointData j) (jointData_section j)

/-- Every actual relative strict K-zero class comes from an original strict K-zero class. -/
theorem changeWeak_KMap_zero_surjective : Function.Surjective (KMap (changeWeak_exact (nested j)) 0)
  :=
  changeWeak_KMap_zero_surjective_of_weak (nested j) (canonicalFiberMap_weak j)

/-- Relative restriction has exactly the image of the original strict restriction homomorphism. -/
theorem range_relativeKRestrict_zero :
    (relativeKRestrict j 0).range = (strictKRestrict j 0).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := changeWeak_KMap_zero_surjective j a
    exact ⟨b, (DFunLike.congr_fun (relativeKRestrict_comp_changeWeak j 0) b).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨KMap (changeWeak_exact (nested j)) 0 a,
      DFunLike.congr_fun (relativeKRestrict_comp_changeWeak j 0) a⟩

/-- The honest subgroup of original extendible strict K-zero classes. -/
abbrev KZeroImage := (strictKRestrict j 0).range

/-- The original relative restriction, codrestricted only to its proved actual image. -/
def relativeKZeroToImage : (coarseWaldhausen j).K 0 →* KZeroImage j :=
  (relativeKRestrict j 0).codRestrict (KZeroImage j) (fun a ↦ by
    change relativeKRestrict j 0 a ∈ (strictKRestrict j 0).range
    rw [← range_relativeKRestrict_zero j]
    exact ⟨a, rfl⟩)

/-- Forgetting subgroup membership recovers the original relative restriction literally. -/
@[simp] theorem relativeKZeroToImage_coe (a : (coarseWaldhausen j).K 0) :
    (relativeKZeroToImage j a : StrictK U 0) = relativeKRestrict j 0 a := rfl

/-- The map to the honest image is genuinely surjective for every original open immersion. -/
theorem relativeKZeroToImage_surjective : Function.Surjective (relativeKZeroToImage j) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨KMap (changeWeak_exact (nested j)) 0 a, ?_⟩
  apply Subtype.ext
  exact DFunLike.congr_fun (relativeKRestrict_comp_changeWeak j 0) a

end Quillen.PerfectComplexes.StrictOpenWeakImage
