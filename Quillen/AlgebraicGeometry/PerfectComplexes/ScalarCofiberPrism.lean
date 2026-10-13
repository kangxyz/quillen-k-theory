/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiber
public import Quillen.Waldhausen.Fibration.CofiberPrismFiber

/-!
# The original scalar-cofiber prism after open restriction

The actual scalar factorization has a fine weak projection. The original scalar is coarse weak
because its restriction is the specified global unit, so two-out-of-three proves that the actual
cofibration factor is coarse weak. Its original quotient square therefore supplies the previously
constructed continuous cofiber prism and canonical-fiber face. The source scalar need not be a unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry unitInterval
open scoped Topology
open Quillen.Waldhausen Quillen.Waldhausen.SplitFactorization Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The literal first factor of the original scalar extension. -/
def perfectScalarInclusion (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    K ⟶ (ExtensionCategory.middle (perfectWaldhausen X)).obj (perfectScalarExtension X r K) :=
  (ExtensionCategory.inclusion (perfectWaldhausen X)).app (perfectScalarExtension X r K)

/-- The literal weak projection from the original scalar factorization. -/
def perfectScalarProjection (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    (ExtensionCategory.middle (perfectWaldhausen X)).obj (perfectScalarExtension X r K) ⟶ K :=
  (splitSubcategoryFunctorialFactorization (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f)).projection.app
      (Arrow.mk ((perfectGlobalScalar X r).app K))

/-- The two original factors compose to the original scalar endomorphism. -/
theorem perfectScalarInclusion_projection (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    perfectScalarInclusion X r K ≫ perfectScalarProjection X r K =
      (perfectGlobalScalar X r).app K :=
  (splitSubcategoryFunctorialFactorization (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f)).factorization
      (Arrow.mk ((perfectGlobalScalar X r).app K))

/-- The unchanged projection is weak already in the original fine perfect structure. -/
theorem perfectScalarProjection_weak (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    (perfectWaldhausen X).weq (perfectScalarProjection X r K) :=
  (splitSubcategoryFunctorialFactorization (locallyPerfect X)
    (fun hA hB f => locallyPerfect_mappingCone hA hB f)).weak
      (Arrow.mk ((perfectGlobalScalar X r).app K))

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- The original cofibration factor is coarse weak by its actual projection and scalar composite. -/
theorem perfectScalarInclusion_openWeak (K : Perfect X) :
    (perfectOpenNested j).coarse.weq (perfectScalarInclusion X r K) := by
  apply (perfectOpenNested j).coarse.weq.of_postcomp
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))
  rw [perfectScalarInclusion_projection]
  exact perfectGlobalScalar_openWeak j r q hq K

/-- The unchanged categorical quotient is the genuine zero-pushout of the original factor. -/
theorem perfectScalarCofiber_isPushout (K : Perfect X) :
    IsPushout (perfectScalarInclusion X r K) (0 : K ⟶ (perfectOpenNested j).coarse.zero)
      ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
      (0 : (perfectOpenNested j).coarse.zero ⟶
        (ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K)) := by
  have h := ExtensionCategory.cofiber_isPushout (perfectWaldhausen X)
    (perfectScalarExtension X r K)
  convert h using 1 <;> first
    | rfl
    | exact (perfectWaldhausen X).isZero.eq_of_tgt _ _
    | exact (perfectWaldhausen X).isZero.eq_of_src _ _

/-- The original first factor remains the same cofibration in the coarse open structure. -/
theorem perfectScalarInclusion_openCof (K : Perfect X) :
    (perfectOpenNested j).coarse.cof (perfectScalarInclusion X r K) :=
  ExtensionCategory.inclusion_cof (perfectWaldhausen X) (perfectScalarExtension X r K)

/-- The actual scalar factorization supplies the full original three-parameter cofiber cube. -/
def perfectOpenScalarCofiberCompositionCube (K : Perfect X) :
    C(unitInterval × (unitInterval × unitInterval), (perfectOpenNested j).coarse.Delooping) :=
  (perfectOpenNested j).coarse.cofiberPrismCompositionCube (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof j r K) (perfectScalarInclusion_openWeak j r q hq K)
    (perfectScalarCofiber_isPushout j r K)

/-- Its comparison-zero face is the original source prefix and original categorical-cofiber fiber.
-/
theorem perfectOpenScalarCofiberCompositionCube_zero (K : Perfect X) (t s : unitInterval) :
    perfectOpenScalarCofiberCompositionCube j r q hq K (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        (perfectOpenNested j).coarse.kZeroObjectLoop K
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop (perfectOpenNested j) (perfectOpenScalarCofiberAcyclic j r q hq K)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  cofiberPrismCompositionCube_zero_fiber (perfectOpenNested j) (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof j r K) (perfectScalarInclusion_openWeak j r q hq K)
    (perfectScalarCofiber_isPushout j r K) t s

/-- The same specified family is a jointly continuous square of original based loops. -/
def perfectOpenScalarCofiberCompositionLoops (K : Perfect X) :
    C(unitInterval × unitInterval,
      Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint) :=
  (perfectOpenNested j).coarse.cofiberPrismCompositionLoops (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof j r K) (perfectScalarInclusion_openWeak j r q hq K)
    (perfectScalarCofiber_isPushout j r K)

/-- Every original comparison, nerve and object-loop coordinate is unchanged. -/
theorem perfectOpenScalarCofiberCompositionLoops_apply (K : Perfect X) (a s t : unitInterval) :
    perfectOpenScalarCofiberCompositionLoops j r q hq K (a, s) t =
      perfectOpenScalarCofiberCompositionCube j r q hq K (a, s, t) := rfl

end Quillen.PerfectComplexes
