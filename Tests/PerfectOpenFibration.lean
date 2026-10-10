/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence

/-! Semantic consumers for actual local shifts, relative weak classes, unchanged
joint cylinders, the original fiber map and the coarse-only connective sequence. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

-- Arbitrary integer, with no strict-global model or scheme finiteness hypothesis.
example {K : Complex X} (hK : locallyPerfect X K) (n : ℤ) :
    locallyPerfect X (K⟦n⟧) := locallyPerfect_shift hK n

example {K : Complex X} (hK : locallyPerfect X K) :
    locallyPerfect X (K⟦(-37 : ℤ)⟧) := locallyPerfect_shift hK (-37)

example : (perfectOpenWeakWaldhausen j).cof = (perfectWaldhausen X).cof := rfl

example : (perfectOpenWeakWaldhausen j).zero = (perfectWaldhausen X).zero := rfl

example {K L : Perfect X} (f : K ⟶ L) :
    (perfectOpenWeakWaldhausen j).weq f ↔ QuasiIso ((restrict j).map f.hom) := Iff.rfl

example {K L : Perfect X} (f : K ⟶ L) [QuasiIso f.hom] :
    (perfectOpenWeakWaldhausen j).weq f :=
  (perfectOpenNested j).le_weq _ (inferInstanceAs (QuasiIso f.hom))

example : (perfectOpenWeakWaldhausen j).weq.HasTwoOutOfThreeProperty := inferInstance

example : ExtensionAxiom (perfectOpenWeakWaldhausen j) :=
  perfectOpenWeakWaldhausen_extensionAxiom j

example : IsExact (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
    (perfectWaldhausen U).cof (perfectWaldhausen U).weq (perfectRestrict j) :=
  perfectOpenRestrict_waldhausenExact j

-- The fine class in the actual joint cylinder is quasi-isomorphism.
example : IsExact (ArrowCategory.waldhausenStructure (perfectWaldhausen X)).cof
    (ArrowCategory.waldhausenStructure (perfectWaldhausen X)).weq
    (ExtensionCategory.waldhausenStructure (perfectWaldhausen X)).cof
    (ExtensionCategory.waldhausenStructure (perfectWaldhausen X)).weq
    (perfectOpenJointData j).joint := (perfectOpenJointData j).exact

example (f : Arrow (Perfect X)) :
    QuasiIso ((restrict j).map ((perfectOpenJointData j).projection.app f).hom) :=
  (perfectOpenJointData j).weak f

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj (perfectWaldhausen X) n)) :
    (RowFactorization.targetInclusion (perfectOpenNested j) (perfectOpenJointData j) n).app f ≫
      (RowFactorization.factorization (perfectOpenNested j) (perfectOpenJointData j)
        n).projection.app f =
      𝟙 f.right :=
  RowFactorization.targetInclusion_projection (perfectOpenNested j) (perfectOpenJointData j)
    (perfectOpenJointData_secondEndpointSection j) f

example {n : SimplexCategory} (f : Arrow (QuotientRows.Obj (perfectWaldhausen X) n)) :
    (RowWeakEquivalences.coarseStructure (perfectOpenNested j) n).weq
      ((RowFactorization.targetInclusion (perfectOpenNested j) (perfectOpenJointData j) n).app f) :=
  RowFactorization.targetInclusion_weak (perfectOpenNested j) (perfectOpenJointData j)
    (perfectOpenJointData_secondEndpointSection j) f

-- The theorem is about the original map and original complete nullhomotopy path.
example : IsWeakHomotopyEquivalence (canonicalFiberMap (perfectOpenNested j)) :=
  perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j

example (a : (acyclicStructure (perfectOpenNested j)).Delooping) :
    (canonicalFiberMap (perfectOpenNested j) a).1.1 =
      acyclicInclusionMap (perfectOpenNested j) a := rfl

example (a : (acyclicStructure (perfectOpenNested j)).Delooping) (t : unitInterval) :
    (canonicalFiberMap (perfectOpenNested j) a).1.2 t =
      acyclicNullhomotopy (perfectOpenNested j) (t, a) := rfl

example (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) = perfectKRestrict j n :=
  perfectOpenKRestrict_comp_perfectOpenKMap j n

example (n : ℕ) : Function.Bijective (perfectSupportedFiberKMap j n) :=
  perfectSupportedFiberKMap_bijective j n

example (n : ℕ) :
    (perfectOpenKMap j (n + 1)).range = (perfectOpenConnectingHom j n).ker ∧
    (perfectOpenConnectingHom j n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range = (perfectOpenKMap j n).ker :=
  perfectOpen_positiveLongExactSequence j n

-- Degree zero retains the relative target. It does not replace it with PerfectK U.
example (x : PerfectOpenK j 0) : ∃ y : PerfectK X 0, perfectOpenKMap j 0 y = x :=
  perfectOpenKMap_zero_surjective j x
