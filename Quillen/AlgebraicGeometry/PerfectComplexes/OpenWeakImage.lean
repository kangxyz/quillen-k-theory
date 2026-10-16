/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.WeakImageKEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenKZeroImage
public import Quillen.Waldhausen.Fibration.Rows.CoarseJoint
public import Quillen.Waldhausen.Fibration.ComplexChainReplacement
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! # Relative-open approximation onto the actual witnessed restriction image

The sole unproved geometric input is strict map factorization when the target
already carries an actual quasi-isomorphism from a restricted perfect complex.
No assertion is made that this input holds for an arbitrary open immersion.
The actual cone cylinder supplies cofibrations and joint data. Thus this
restricted input constructs the inherited image category and compares the
original relative endpoint to it, retaining the original target inclusion and
its precise degree-zero image. Density of the inclusion remains separate.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.PerfectComplexes
open Waldhausen
namespace OpenWeakImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual full subcategory of perfect targets admitting a quasi-isomorphism
from an original restriction. This is a one-arrow witnessed image. -/
abbrev Obj := ApproximationImage.Obj (perfectWaldhausen U) (perfectRestrict j)

/-- The geometric lifting input is restricted to targets with an actual
comparison witness; no source cofibration is demanded at this stage. -/
def HasMapFactorization : Prop :=
  ∀ {A : Perfect X} {B : Perfect U} (f : (perfectRestrict j).obj A ⟶ B)
    (E : Perfect X) (q : (perfectRestrict j).obj E ⟶ B),
    (perfectWaldhausen U).weq q →
      ∃ (A' : Perfect X) (a : A ⟶ A') (p : (perfectRestrict j).obj A' ⟶ B),
        (perfectWaldhausen U).weq p ∧ (perfectRestrict j).map a ≫ p = f

/-- The original identity-cone factorization is a genuine coarse-source factorization. -/
def sourceFactorization : FunctorialFactorization (perfectOpenWeakWaldhausen j) := by
  let T := Fibration.complexSubcategoryFactorization (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f)
  exact { T with weak := fun f ↦ (perfectOpenNested j).le_weq _ (T.weak f) }

variable {j} (h : HasMapFactorization j)

include h in
/-- Coarse reflection is definitional; the genuine cone cylinder upgrades just
the restricted geometric map factorization to actual App2 on the weak image. -/
theorem approximationOnImage : ApproximationImage.HasApproximationOnImage
    (perfectOpenWeakWaldhausen j) (perfectWaldhausen U) (perfectRestrict j) :=
  ApproximationImage.HasApproximationOnImage.of_factorization _ _ _
    (sourceFactorization j) (perfectOpenRestrict_waldhausenExact j).weak (fun _ hf ↦ hf)
    (fun f hB ↦ by obtain ⟨E, q, hq⟩ := hB; exact h f E q hq)

/-- The genuine inherited target structure, with actual restriction-image objects. -/
def waldhausenStructure : Structure (Obj j) :=
  ApproximationImage.waldhausenStructure (approximationOnImage h)
    (perfectOpenRestrict_waldhausenExact j)

/-- Original restriction corestricts exactly to the constructed witnessed image. -/
theorem corestrict_exact : IsExact (perfectOpenWeakWaldhausen j).cof
    (perfectOpenWeakWaldhausen j).weq (waldhausenStructure h).cof (waldhausenStructure h).weq
    (ApproximationImage.corestrict (perfectWaldhausen U) (perfectRestrict j)) :=
  ApproximationImage.corestrict_exact (approximationOnImage h)
    (perfectOpenRestrict_waldhausenExact j)

/-- The literal inclusion retains actual perfect-complex cofibrations and quasi-isomorphisms. -/
theorem inclusion_exact : IsExact (waldhausenStructure h).cof (waldhausenStructure h).weq
    (perfectWaldhausen U).cof (perfectWaldhausen U).weq
    (ApproximationImage.objects (perfectWaldhausen U) (perfectRestrict j)).ι :=
  ApproximationImage.inclusion_exact (approximationOnImage h)
    (perfectOpenRestrict_waldhausenExact j)

include h in
/-- Complete weakness of the actual corestriction S-map, conditional only on the
restricted geometric map-factorization statement. -/
theorem corestrict_deloopingMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (deloopingMap (corestrict_exact h)).hom := by
  let : (perfectWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (locallyPerfect U)).HasTwoOutOfThreeProperty
  exact ApproximationImage.corestrict_deloopingMap_isWeakHomotopyEquivalence
    (approximationOnImage h) (perfectOpenRestrict_waldhausenExact j)
    ((perfectOpenJointData j).coarseReflexive (perfectOpenNested j))

/-- The relative endpoint and the actual witnessed-image K-groups agree via
original restriction. No assertion about inclusion cofinality is made. -/
def KEquiv (n : ℕ) : PerfectOpenK j n ≃* (waldhausenStructure h).K n :=
  KEquivOfWeakRealization (corestrict_exact h)
    (corestrict_deloopingMap_isWeakHomotopyEquivalence h) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KEquiv_coe (n : ℕ) :
    ↑(KEquiv h n) = KMap (corestrict_exact h) n := rfl

/-- Composing with the literal target inclusion recovers actual relative restriction. -/
theorem inclusion_KMap_comp (n : ℕ) :
    (KMap (inclusion_exact h) n).comp (KMap (corestrict_exact h) n) =
      perfectOpenKRestrict j n :=
  ApproximationImage.inclusion_KMap_comp_corestrict (approximationOnImage h)
    (perfectOpenRestrict_waldhausenExact j) n

/-- The inclusion's degree-zero image is exactly the actual original restriction
image from X, rather than all target K-zero. -/
theorem range_inclusion_KMap_zero :
    (KMap (inclusion_exact h) 0).range = (perfectKRestrict j 0).range := by
  let : (perfectWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (locallyPerfect U)).HasTwoOutOfThreeProperty
  exact (ApproximationImage.range_inclusion_KMap (approximationOnImage h)
    (perfectOpenRestrict_waldhausenExact j)
    ((perfectOpenJointData j).coarseReflexive (perfectOpenNested j)) 0).trans
      (range_perfectOpenKRestrict_zero j)

end OpenWeakImage
end Quillen.PerfectComplexes
