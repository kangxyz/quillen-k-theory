/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.PerfectSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.SplitFactorization
public import Quillen.Waldhausen.Fibration.GeneralComparison
public import Quillen.Waldhausen.Fibration.LongExactSequence
public import Quillen.Waldhausen.Fibration.ComplexExtension
public import Quillen.Waldhausen.Fibration.InverseImageWeak
public import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-!
# The genuine relative-open Waldhausen fibration for perfect complexes

For an arbitrary open immersion, this file changes only the weak equivalences
on the actual category of locally perfect complexes. Relative weak equivalences
are the chain maps that become quasi-isomorphisms after actual open restriction.
Local strict models prove closure under every integer shift. Together with the
existing actual mapping cones this supplies genuine joint cylinder data and
the canonical relative-coarse fiber theorem in the original category universes.

The coarse target remains the named relative Waldhausen model on `Perfect X`.
No equivalence with `Perfect U`, density, cofinality, or nonconnective
Thomason–Trobaugh localization is asserted here.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Actual open restriction commutes with integer shifts of chain complexes. -/
instance instCommShiftRestrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (restrict j).CommShift ℤ := by
  unfold restrict
  infer_instance

/-- Every integer shift of a genuinely locally perfect complex is locally
perfect, using the shifted actual strict model on the same neighborhood. -/
theorem locallyPerfect_shift {X : Scheme.{u}} {K : Complex X}
    (hK : locallyPerfect X K) (n : ℤ) :
    locallyPerfect X ((shiftFunctor (Complex X) n).obj K) := by
  intro x
  obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK x
  refine ⟨O, hx, ⟨(shiftFunctor (Complex O.toScheme) n).obj P.obj,
    strictPerfect_shift P.property n⟩, ⟨?_⟩⟩
  exact (toDerived O.toScheme).mapIso (((restrict O.ι).commShiftIso n).app K) ≪≫
    ((toDerived O.toScheme).commShiftIso n).app ((restrict O.ι).obj K) ≪≫
    (shiftFunctor (Derived O.toScheme) n).mapIso eP ≪≫
    (((toDerived O.toScheme).commShiftIso n).app P.obj).symm

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original perfect category, cofibrations and chosen zero, with weak
equivalences detected by actual open restriction. -/
def perfectOpenWeakWaldhausen : Waldhausen.Structure (Perfect X) :=
  Waldhausen.Structure.withInverseImageWeak (perfectRestrict_waldhausenExact j)

/-- Genuine fine quasi-isomorphisms are contained in the actual relative class. -/
def perfectOpenNested : Waldhausen.Fibration.NestedWeakEquivalences (perfectWaldhausen X) :=
  Waldhausen.Structure.inverseImageWeakNested (perfectRestrict_waldhausenExact j)

@[simp] theorem perfectOpenWeakWaldhausen_cof :
    (perfectOpenWeakWaldhausen j).cof = (perfectWaldhausen X).cof := rfl

@[simp] theorem perfectOpenWeakWaldhausen_zero :
    (perfectOpenWeakWaldhausen j).zero = (perfectWaldhausen X).zero := rfl

/-- The relative weak predicate is precisely quasi-isomorphism on the actual
restricted underlying chain map. -/
@[simp] theorem perfectOpenWeakWaldhausen_weq_iff {K L : Perfect X} (f : K ⟶ L) :
    (perfectOpenWeakWaldhausen j).weq f ↔ QuasiIso ((restrict j).map f.hom) := Iff.rfl

instance perfectOpenWeakWaldhausen_twoOutOfThree :
    (perfectOpenWeakWaldhausen j).weq.HasTwoOutOfThreeProperty := by
  let : (perfectWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (Waldhausen.subcategoryWeakEquivalences
      (locallyPerfect U)).HasTwoOutOfThreeProperty
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    (perfectRestrict_waldhausenExact j)

instance perfectOpenNested_twoOutOfThree :
    (perfectOpenNested j).coarse.weq.HasTwoOutOfThreeProperty :=
  perfectOpenWeakWaldhausen_twoOutOfThree j

/-- The extension axiom follows from actual exact open restriction. -/
theorem perfectOpenWeakWaldhausen_extensionAxiom :
    Waldhausen.Fibration.ExtensionAxiom (perfectOpenWeakWaldhausen j) :=
  Waldhausen.Structure.withInverseImageWeak_extensionAxiom
    (perfectRestrict_waldhausenExact j)
    (Waldhausen.Fibration.complexSubcategory_extensionAxiom (locallyPerfect U))

/-- The original restriction functor is also exact for the relative model. -/
theorem perfectOpenRestrict_waldhausenExact :
    Waldhausen.IsExact (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (perfectWaldhausen U).cof (perfectWaldhausen U).weq (perfectRestrict j) :=
  Waldhausen.Structure.withInverseImageWeak_exact (perfectRestrict_waldhausenExact j)

/-- The actual identity-cone joint cylinder in locally perfect complexes. -/
def perfectOpenJointData : Waldhausen.Fibration.RowFactorization.JointData (perfectOpenNested j) :=
  Waldhausen.Fibration.complexJointDataOfNested (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f)
    (fun _ hK ↦ locallyPerfect_shift hK 1) (perfectOpenNested j)

/-- The actual target endpoint is a section of the original cylinder projection. -/
theorem perfectOpenJointData_secondEndpointSection :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection (perfectOpenNested j)
      (perfectOpenJointData j) :=
  Waldhausen.Fibration.complexJointDataOfNested_secondEndpointSection (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f)
    (fun _ hK ↦ locallyPerfect_shift hK 1) (perfectOpenNested j)

/-- The unchanged original canonical relative-coarse fiber map is a weak
homotopy equivalence, without any common-universe or geometric extra hypothesis. -/
theorem perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (Waldhausen.Fibration.canonicalFiberMap (perfectOpenNested j)) :=
  Waldhausen.Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general
    (perfectOpenNested j) (perfectOpenWeakWaldhausen_extensionAxiom j)
    (perfectOpenJointData j) (perfectOpenJointData_secondEndpointSection j)

/-- Connective K-theory of the named relative-open coarse model. -/
abbrev PerfectOpenK (n : ℕ) := (perfectOpenWeakWaldhausen j).K n

/-- The original change-of-weak-equivalences map, on the unchanged perfect category. -/
def perfectOpenKMap (n : ℕ) : PerfectK X n →* PerfectOpenK j n :=
  Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (perfectOpenNested j)) n

/-- Restriction from the relative coarse model to actual perfect complexes on the open. -/
def perfectOpenKRestrict (n : ℕ) : PerfectOpenK j n →* PerfectK U n :=
  Waldhausen.KMap (perfectOpenRestrict_waldhausenExact j) n

/-- The original open-restriction K-map factors through the named coarse model. -/
theorem perfectOpenKRestrict_comp_perfectOpenKMap (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) = perfectKRestrict j n := by
  unfold perfectOpenKRestrict perfectOpenKMap perfectKRestrict
  rw [Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes
