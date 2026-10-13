/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalScalar
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenConeFiberLoop

/-!
# Scalars invertible on an open and their original supported cones

Only the restricted scalar is required to be a unit. Its original global endomorphism is
open-weak, and gives the actual relative-open cylinder and supported mapping-cone fiber loop.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes

/-- A scalar which is a unit gives precisely the existing original unit automorphism. -/
theorem complexGlobalScalar_unit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (K : Complex X) :
    (complexGlobalScalar X (↑r)).app K = (complexGlobalUnitIso X r).hom.app K := by
  ext n : 1
  exact (complexGlobalUnitIso_original_terms X r K n).symm

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- Restriction of the original scalar is the exact preexisting unit automorphism. -/
theorem restrict_map_complexGlobalScalar_unit (K : Complex X) :
    (restrict j).map ((complexGlobalScalar X r).app K) =
      (complexGlobalUnitIso U q).hom.app ((restrict j).obj K) := by
  rw [restrict_map_complexGlobalScalar, hq, complexGlobalScalar_unit]

include hq in
/-- The original endomorphism is genuinely weak after restriction to the specified open. -/
theorem perfectGlobalScalar_openWeak (K : Perfect X) :
    (perfectOpenWeakWaldhausen j).weq ((perfectGlobalScalar X r).app K) := by
  rw [perfectOpenWeakWaldhausen_weq_iff]
  change QuasiIso ((restrict j).map ((complexGlobalScalar X r).app K.obj))
  rw [restrict_map_complexGlobalScalar, hq, complexGlobalScalar_unit]
  infer_instance

/-- The actual scalar cylinder is the original change-of-weak-equivalences transformation track.
-/
def perfectOpenScalarTrack (K : Perfect X) :
    ((perfectOpenWeakWaldhausen j).kZeroObjectLoop K).Homotopy
      ((perfectOpenWeakWaldhausen j).kZeroObjectLoop K) :=
  objectTransformationTrack (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
    (changeWeak_exact (perfectOpenNested j)) (changeWeak_exact (perfectOpenNested j))
    (perfectGlobalScalar X r) (perfectGlobalScalar_openWeak j r q hq) rfl rfl K

/-- The supported cone is the unchanged complex of the original, possibly noninvertible scalar.
-/
def perfectOpenScalarCone (K : Perfect X) : AcyclicCategory (perfectOpenNested j) :=
  perfectOpenMappingConeAcyclic j ((perfectGlobalScalar X r).app K)
    (perfectGlobalScalar_openWeak j r q hq K)

/-- On every original term the source scalar is literal multiplication by the global function. -/
theorem perfectOpenScalarCone_original (K : Perfect X) :
    (perfectOpenScalarCone j r q hq K).obj.obj =
      CochainComplex.mappingCone ((complexGlobalScalar X r).app K.obj) := rfl

/-- Both parameters of the original scalar transformation cylinder remain literal. -/
theorem perfectOpenScalarTrack_apply (K : Perfect X) (s t : unitInterval) :
    perfectOpenScalarTrack j r q hq K (s, t) =
      weakNaturalTransformationRealizationHomotopy
        (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (changeWeak_exact (perfectOpenNested j)) (changeWeak_exact (perfectOpenNested j))
        (perfectGlobalScalar X r) (perfectGlobalScalar_openWeak j r q hq)
        (s, (perfectWaldhausen X).kZeroObjectLoop K t) := rfl

end Quillen.PerfectComplexes
