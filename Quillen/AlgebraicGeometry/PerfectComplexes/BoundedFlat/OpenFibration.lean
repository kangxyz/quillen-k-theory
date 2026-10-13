/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence

/-! # The actual relative-open bounded-flat fibration and its supported boundary -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance boundedFlatPerfectOpenNested_twoOutOfThree :
    (boundedFlatPerfectOpenNested j).coarse.weq.HasTwoOutOfThreeProperty := by
  let : (perfectWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (Waldhausen.subcategoryWeakEquivalences (locallyPerfect
      U)).HasTwoOutOfThreeProperty
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    ((boundedFlatPerfectInclusion_exact X).comp (perfectRestrict_waldhausenExact j))

/-- Exact restriction proves the genuine coarse extension axiom. -/
theorem boundedFlatPerfectOpenWaldhausen_extensionAxiom :
    ExtensionAxiom (boundedFlatPerfectOpenWaldhausen j) :=
  Structure.withInverseImageWeak_extensionAxiom
    ((boundedFlatPerfectInclusion_exact X).comp (perfectRestrict_waldhausenExact j))
    (complexSubcategory_extensionAxiom (locallyPerfect U))

/-- The actual second cylinder endpoint is a section of its original projection. -/
theorem boundedFlatPerfectOpenJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (boundedFlatPerfectOpenNested j)
      (boundedFlatPerfectOpenJointData j) :=
  complexJointDataOfNested_secondEndpointSection (boundedFlatPerfect X)
    (fun hK hL f => boundedFlatPerfect_mappingCone hK hL f)
    (fun _ hK => boundedFlatPerfect_shift hK 1) (boundedFlatPerfectOpenNested j)

/-- The original bounded-flat relative canonical fiber comparison is genuinely weak. -/
theorem boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedFlatPerfectOpenNested j)) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedFlatPerfectOpenNested j)
    (boundedFlatPerfectOpenWaldhausen_extensionAxiom j) (boundedFlatPerfectOpenJointData j)
    (boundedFlatPerfectOpenJointData_secondEndpointSection j)

/-- The genuine original homotopy-fiber boundary with supported bounded-flat target. -/
def boundedFlatPerfectOpenConnectingHom (n : ℕ) :
    BoundedFlatPerfectOpenK j (n+1) →* BoundedFlatPerfectSupportedK j n :=
  (boundedFlatPerfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
    (changeWeakConnectingHom (boundedFlatPerfectOpenNested j)
      (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n)

end Quillen.PerfectComplexes
