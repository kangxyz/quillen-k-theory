/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Cone
public import Quillen.Waldhausen.Fibration.GeneralComparison
public import Quillen.Waldhausen.Fibration.ComplexExtension
public import Quillen.Waldhausen.Fibration.InverseImageWeak
public import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-! # Genuine relative-open fibration with prescribed original support -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original supported perfect category, cofibrations and chosen zero, with weak
equivalences detected by actual open restriction. -/
def perfectSupportedOpenWeakWaldhausen : Waldhausen.Structure (perfectSupported T.ι).FullSubcategory
  :=
  Waldhausen.Structure.withInverseImageWeak (perfectSupportedRestrict_exact j T)

/-- Genuine fine quasi-isomorphisms are contained in the actual relative class. -/
def perfectSupportedOpenNested : Waldhausen.Fibration.NestedWeakEquivalences
  (perfectSupportedWaldhausen T.ι) :=
  Waldhausen.Structure.inverseImageWeakNested (perfectSupportedRestrict_exact j T)

@[simp] theorem perfectSupportedOpenWeakWaldhausen_cof :
    (perfectSupportedOpenWeakWaldhausen j T).cof = (perfectSupportedWaldhausen T.ι).cof := rfl

@[simp] theorem perfectSupportedOpenWeakWaldhausen_zero :
    (perfectSupportedOpenWeakWaldhausen j T).zero = (perfectSupportedWaldhausen T.ι).zero := rfl

/-- The relative weak predicate is precisely quasi-isomorphism on the actual
restricted underlying chain map. -/
@[simp] theorem perfectSupportedOpenWeakWaldhausen_weq_iff {K L : (perfectSupported
  T.ι).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedOpenWeakWaldhausen j T).weq f ↔ QuasiIso ((restrict j).map f.hom) := Iff.rfl

instance perfectSupportedOpenWeakWaldhausen_twoOutOfThree :
    (perfectSupportedOpenWeakWaldhausen j T).weq.HasTwoOutOfThreeProperty := by
  let : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (Waldhausen.subcategoryWeakEquivalences
      (perfectSupported (j ⁻¹ᵁ T).ι)).HasTwoOutOfThreeProperty
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    (perfectSupportedRestrict_exact j T)

instance perfectSupportedOpenNested_twoOutOfThree :
    (perfectSupportedOpenNested j T).coarse.weq.HasTwoOutOfThreeProperty :=
  perfectSupportedOpenWeakWaldhausen_twoOutOfThree j T

/-- The extension axiom follows from actual exact open restriction. -/
theorem perfectSupportedOpenWeakWaldhausen_extensionAxiom :
    Waldhausen.Fibration.ExtensionAxiom (perfectSupportedOpenWeakWaldhausen j T) :=
  Waldhausen.Structure.withInverseImageWeak_extensionAxiom
    (perfectSupportedRestrict_exact j T)
    (Waldhausen.Fibration.complexSubcategory_extensionAxiom (perfectSupported (j ⁻¹ᵁ T).ι))

/-- The original restriction functor is also exact for the relative model. -/
theorem perfectSupportedOpenRestrict_waldhausenExact :
    Waldhausen.IsExact (perfectSupportedOpenWeakWaldhausen j T).cof
      (perfectSupportedOpenWeakWaldhausen j T).weq
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
        (perfectSupportedRestrict j T) :=
  Waldhausen.Structure.withInverseImageWeak_exact (perfectSupportedRestrict_exact j T)

/-- The actual identity-cone joint cylinder in supported locally perfect complexes. -/
def perfectSupportedOpenJointData : Waldhausen.Fibration.RowFactorization.JointData
  (perfectSupportedOpenNested j T) :=
  Waldhausen.Fibration.complexJointDataOfNested (perfectSupported T.ι)
    (fun hK hL f ↦ perfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK ↦ perfectSupported_shift T.ι hK 1) (perfectSupportedOpenNested j T)

/-- The actual target endpoint is a section of the original cylinder projection. -/
theorem perfectSupportedOpenJointData_secondEndpointSection :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection (perfectSupportedOpenNested j T)
      (perfectSupportedOpenJointData j T) :=
  Waldhausen.Fibration.complexJointDataOfNested_secondEndpointSection (perfectSupported T.ι)
    (fun hK hL f ↦ perfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK ↦ perfectSupported_shift T.ι hK 1) (perfectSupportedOpenNested j T)

/-- The unchanged original canonical relative-coarse fiber map is a weak
homotopy equivalence, without any common-universe or geometric extra hypothesis. -/
theorem perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (Waldhausen.Fibration.canonicalFiberMap (perfectSupportedOpenNested j T)) :=
  Waldhausen.Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general
    (perfectSupportedOpenNested j T) (perfectSupportedOpenWeakWaldhausen_extensionAxiom j T)
    (perfectSupportedOpenJointData j T) (perfectSupportedOpenJointData_secondEndpointSection j T)

/-- Connective K-theory of the named relative-open coarse model. -/
abbrev PerfectSupportedOpenK (n : ℕ) := (perfectSupportedOpenWeakWaldhausen j T).K n

/-- The original change-of-weak-equivalences map, on the unchanged perfect category. -/
def perfectSupportedOpenKMap (n : ℕ) : PerfectSupportedK T.ι n →* PerfectSupportedOpenK j T n :=
  Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (perfectSupportedOpenNested j T)) n

/-- Restriction from the relative coarse model to actual perfect complexes on the open. -/
def perfectSupportedOpenKRestrict (n : ℕ) : PerfectSupportedOpenK j T n →* PerfectSupportedK (j ⁻¹ᵁ
  T).ι n :=
  Waldhausen.KMap (perfectSupportedOpenRestrict_waldhausenExact j T) n

/-- The original open-restriction K-map factors through the named coarse model. -/
theorem perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap (n : ℕ) :
    (perfectSupportedOpenKRestrict j T n).comp (perfectSupportedOpenKMap j T n) =
      perfectSupportedKRestrict j T n := by
  unfold perfectSupportedOpenKRestrict perfectSupportedOpenKMap perfectSupportedKRestrict
  rw [Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes
