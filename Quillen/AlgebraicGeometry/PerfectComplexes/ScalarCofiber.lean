/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenScalarUnit
public import Quillen.Waldhausen.SplitComplexes.FactorizationCofiber

/-!
# The actual perfect scalar extension and its supported cofiber

The original split factorization supplies a genuine extension-category object. When the scalar
is invertible on the original open, its actual cofiber is canonically the previously constructed
supported mapping cone, with the original quotient map and cone sign retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original scalar's split-cofibration factor is an actual perfect extension object. -/
def perfectScalarExtension (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    ExtensionCategory.Obj (perfectWaldhausen X) :=
  subcategoryExtension (locallyPerfect X) (fun hA hB f => locallyPerfect_mappingCone hA hB f)
    ((perfectGlobalScalar X r).app K)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Its genuine categorical cofiber is the unchanged supported scalar cone. -/
def perfectOpenScalarCofiberIso (K : Perfect X) :
    (ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K) ≅
      (perfectOpenScalarCone j r q hq K).obj :=
  subcategoryCofiberConeIso (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f) ((perfectGlobalScalar X r).app K)

/-- The original quotient becomes exactly the signed mapping-cone quotient, with no new choice. -/
theorem perfectOpenScalarCofiberIso_quotient (K : Perfect X) :
    (ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K) ≫
        (perfectOpenScalarCofiberIso j r q hq K).hom =
      (locallyPerfect X).homMk
        (quotientToCone ((complexGlobalScalar X r).app K.obj)) :=
  subcategoryCofiberConeIso_quotient (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f) ((perfectGlobalScalar X r).app K)

/-- The actual categorical cofiber itself lies in the original relative-acyclic category. -/
def perfectOpenScalarCofiberAcyclic (K : Perfect X) : AcyclicCategory (perfectOpenNested j) :=
  ⟨(ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K),
    acyclic_of_iso (perfectOpenWeakWaldhausen j) (perfectOpenScalarCone j r q hq K).property
      (perfectOpenScalarCofiberIso j r q hq K).symm⟩

/-- The same original comparison is an isomorphism in the actual relative-acyclic category. -/
def perfectOpenScalarCofiberAcyclicIso (K : Perfect X) :
    perfectOpenScalarCofiberAcyclic j r q hq K ≅ perfectOpenScalarCone j r q hq K :=
  (acyclicObjects (perfectOpenNested j)).isoMk (perfectOpenScalarCofiberIso j r q hq K)

/-- Their original relative-acyclic object classes agree through this specified isomorphism. -/
theorem perfectOpenScalarCofiberAcyclic_class (K : Perfect X) :
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic j r q hq K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone j r q hq K) :=
  (acyclicStructure (perfectOpenNested j)).kZeroObjectClass_iso
    (perfectOpenScalarCofiberAcyclicIso j r q hq K)

end Quillen.PerfectComplexes
