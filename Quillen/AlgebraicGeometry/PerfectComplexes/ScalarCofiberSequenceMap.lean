/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFunctor
public import Quillen.Waldhausen.Additivity.IdentitySequence
public import Quillen.Waldhausen.Additivity.ChangeWeakEndpointHomotopies
public import Quillen.Waldhausen.Fibration.CanonicalFiberMap

/-!
# The literal identity-to-scalar map of cofibration sequences

The source is identity-to-identity-to-the-chosen-zero. The target is the original scalar
cylinder with its signed literal cone. Vertical components are identity, the original inclusion,
and exactly the zero-to-acyclic-inclusion transformation whiskered by the actual acyclic cone
functor. All inherited cofibrations and the original fine weak projection remain unchanged.
These are categorical input data for a separately constructed based-additivity square.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The source sequence uses the exact original chosen-zero map in the coarse structure. -/
theorem perfectOpenScalarIdentityCofibrationSequence :
    IsCofibrationSequence (perfectWaldhausen X) (perfectOpenNested j).coarse
      (𝟙 (𝟭 (Perfect X))) (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) :=
  identityCofibrationSequence (perfectOpenNested j).coarse (𝟭 (Perfect X))
    (perfectWaldhausen X) (changeWeak_exact (perfectOpenNested j))

/-- The target retains the original cylinder, signed cone and inherited relative cofibrations. -/
theorem perfectOpenScalarCofibrationSequence (r : Γ(X, ⊤)) :
    IsCofibrationSequence (perfectWaldhausen X) (perfectOpenNested j).coarse
      (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r) :=
  isCofibrationSequence_changeWeak (perfectWaldhausen X) (perfectWaldhausen X)
    (perfectOpenNested j) (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
    (perfectScalarCofibrationSequence X r)

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The quotient component is the original zero-to-inclusion on the actual cone functor. -/
def perfectOpenScalarZeroToCone :
    zeroFunctor (C := Perfect X) (perfectOpenNested j).coarse ⟶ perfectScalarConeFunctor X r :=
  Functor.whiskerLeft (perfectOpenScalarConeFunctor j r q hq)
    (zeroToAcyclicInclusion (perfectOpenNested j))

/-- Every component retains the specified coarse zero and the same literal scalar cone. -/
theorem perfectOpenScalarZeroToCone_app (K : Perfect X) :
    (perfectOpenScalarZeroToCone j r q hq).app K =
      (perfectOpenNested j).coarse.isZero.to_ ((perfectScalarConeFunctor X r).obj K) := rfl

/-- The entire quotient square is the reversed commutation of the original zero-corner pushout. -/
theorem perfectOpenScalarZeroToCone_sequence :
    QuotientRows.oneIdToZero (perfectOpenNested j).coarse ≫
        perfectOpenScalarZeroToCone j r q hq =
      perfectScalarInclusionNat X r ≫ perfectScalarConeProjectionNat X r := by
  apply NatTrans.ext
  funext K
  exact ((perfectOpenScalarCofibrationSequence j r).cofiber K).w.symm

/-- Weakness is exactly the preexisting acyclicity witness on the actual cone object. -/
theorem perfectOpenScalarZeroToCone_weak (K : Perfect X) :
    (perfectOpenNested j).coarse.weq ((perfectOpenScalarZeroToCone j r q hq).app K) :=
  zeroToAcyclicInclusion_weak (perfectOpenNested j)
    ((perfectOpenScalarConeFunctor j r q hq).obj K)

include hq in
/-- The middle component is the original inclusion, coarse weak by the old scalar factorization. -/
theorem perfectScalarInclusionNat_openWeak (K : Perfect X) :
    (perfectOpenNested j).coarse.weq ((perfectScalarInclusionNat X r).app K) :=
  perfectScalarInclusion_openWeak j r q hq K

/-- The unchanged fine weak projection is carried to the same coarse weak structure. -/
theorem perfectScalarProjectionNat_openWeak (K : Perfect X) :
    (perfectOpenNested j).coarse.weq ((perfectScalarProjectionNat X r).app K) :=
  (perfectOpenNested j).le_weq _ (perfectScalarProjectionNat_weak X r K)

end Quillen.PerfectComplexes
