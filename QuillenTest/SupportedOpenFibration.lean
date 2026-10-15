/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Forget
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.JointComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.JointComparison

/-!
# Supported open fibration regression statements

Records union-support fiber maps, the K₁-to-K₀ exact tail, and the factorization
of restriction through the relative supported model. Further statements concern
cocylinder endpoints and projections, and compatibility of the boundary and
restriction maps with forgetting support.
-/

@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.SupportedOpenFibration
open Quillen Waldhausen Fibration

/-- The actual union-support fiber equivalence retains both the original
complex and every original chain map, in both directions. -/
theorem actual_fiber_maps {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    {A B : AcyclicCategory (perfectSupportedOpenNested j T)} (f : A ⟶ B) :
    ((perfectSupportedOpenAcyclicToSupported j T).obj A).obj = A.obj.obj ∧
    ((perfectSupportedOpenAcyclicToSupported j T).map f).hom = f.hom.hom ∧
    (perfectSupportedUnionToAcyclic j T).map ((perfectSupportedOpenAcyclicToSupported j T).map f) =
      f :=
  ⟨rfl,rfl,rfl⟩

/-- The named relative supported model gives the actual original restriction
homomorphism, including degree zero. -/
theorem original_restriction_factor {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) (n : ℕ) (x : PerfectSupportedK T.ι n) :
    perfectSupportedOpenKRestrict j T n (perfectSupportedOpenKMap j T n x) =
      perfectSupportedKRestrict j T n x :=
  DFunLike.congr_fun (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T n) x

/-- The degree-zero supported fiber projection is literally the original
inclusion from union support, without a local K0 surjectivity premise. -/
theorem original_zero_fiber_projection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) :
    (piMap 0 (HomotopyFiber.projection (changeWeakMap (perfectSupportedOpenNested j T))
      (perfectSupportedOpenWeakWaldhausen j T).kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ (perfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T)))).comp
      (perfectSupportedUnionFiberKMap j T 0) = perfectSupportedUnionKMap j T 0 :=
  perfectSupportedUnionFiberKMap_projection j T 0

/-- The actual K1-to-K0 tail remains exact at every original displayed term. -/
theorem original_relative_zero_tail {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) :
    (perfectSupportedOpenKMap j T 1).range = (perfectSupportedOpenConnectingHom j T 0).ker ∧
    (perfectSupportedOpenConnectingHom j T 0).range = (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedOpenKMap j T 0).ker :=
  perfectSupportedOpen_positiveLongExactSequence j T 0

/-- Both original endpoint maps survive the literal supported restriction
cocylinder comparison simultaneously. -/
theorem original_supported_cocylinder_endpoints {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    (f : Arrow (perfectSupported T.ι).FullSubcategoryᵒᵖ) :
    (perfectSupportedOppositeJointData (j ⁻¹ᵁ T).ι).inl.app ((perfectSupportedRestrict j
      T).op.mapArrow.obj f) ≫
        ((perfectSupportedRestrictOpJointIso j T).inv.app f).hom.left =
      (perfectSupportedRestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inl.app f) ∧
    (perfectSupportedOppositeJointData (j ⁻¹ᵁ T).ι).inr.app ((perfectSupportedRestrict j
      T).op.mapArrow.obj f) ≫
        ((perfectSupportedRestrictOpJointIso j T).inv.app f).hom.left =
      (perfectSupportedRestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inr.app f) :=
  ⟨perfectSupportedRestrictOpJointIso_inv_inl j T f, perfectSupportedRestrictOpJointIso_inv_inr
    j T f⟩

/-- The saturated-image comparison also retains the exact original projection. -/
theorem original_image_cocylinder_projection {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    [Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T)]
    (f : Arrow (perfectSupported T.ι).FullSubcategoryᵒᵖ) :
    ((SupportedOpenDerivedImage.complexCorestrictOpJointIso j T).inv.app f).hom.right ≫
      (SupportedOpenDerivedImage.complexCorestrict j T).op.map
        ((perfectSupportedOppositeJointData T.ι).projection.app f) =
      (SupportedOpenDerivedImage.complexOppositeJointData j T).projection.app
        ((SupportedOpenDerivedImage.complexCorestrict j T).op.mapArrow.obj f) :=
  SupportedOpenDerivedImage.complexCorestrictOpJointIso_inv_projection j T f

/-- The genuine supported K1-to-K0 boundary maps to the already public
perfect boundary under the original support-forgetting maps. -/
theorem original_zero_boundary_forget {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) (x : PerfectSupportedOpenK j T 1) :
    perfectSupportedUnionForgetKMap j T 0 (perfectSupportedOpenConnectingHom j T 0 x) =
      perfectOpenConnectingHom j 0 (perfectSupportedOpenKForget j T 1 x) :=
  DFunLike.congr_fun (perfectSupportedOpenConnectingHom_forget j T 0) x

/-- Following both original relative-model maps and forgetting support agrees
with the existing geometric restriction in every connective degree. -/
theorem original_fine_restriction_forget {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) (n : ℕ) :
    ((perfectOpenKRestrict j n).comp (perfectSupportedOpenKForget j T n)).comp
      (perfectSupportedOpenKMap j T n) = (perfectKRestrict j n).comp (perfectSupportedKMap T.ι n) :=
        by
  rw [MonoidHom.comp_assoc,perfectSupportedOpenKForget_comp_changeWeak,← MonoidHom.comp_assoc,
    perfectOpenKRestrict_comp_perfectOpenKMap]

end QuillenTest.SupportedOpenFibration
