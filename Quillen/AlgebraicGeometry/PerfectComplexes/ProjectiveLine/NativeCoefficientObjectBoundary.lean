/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientKZeroConeClass
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOverlapUnitBoundary

/-!
# Original native unit-boundary coordinates on arbitrary coefficient objects

Original supported excision identifies the actual global coefficient cone with the scalar cone
on the negative native chart. The unchanged Mayer–Vietoris connecting map therefore takes the
forward Laurent unit to the original Phi pair consisting of the inverse coefficient and the
coefficient. No bijectivity of Phi or replacement of the original boundary is used.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

variable (X : QuasiCompactSchemes.{u})

/-- The actual cone comparison lies in the literal overlap-supported category. -/
def coefficientSupportedConeMinusIso (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectSupportedRestrict (nativeMinus.app X).hom (positiveOpen X)).obj
        (coefficientSupportedCone X K) ≅
      (perfectAcyclicToSupported (overlapOpen X).ι).obj
        (perfectOpenScalarCone (overlapOpen X).ι (nativePolynomialCoordinate X)
          (overlapLaurentUnit X)⁻¹ (polynomialCoordinate_overlap X)
          ((perfectRestrict (nativeMinus.app X).hom).obj K)) :=
  (perfectSupported (overlapOpen X).ι).isoMk (coefficientConeMinusIso X K)

/-- Original supported restriction retains the exact scalar-cone object class. -/
theorem coefficientSupportedCone_restrict_class (K : Perfect (nativeLineFunctor.obj X).obj) :
    perfectSupportedKRestrict (nativeMinus.app X).hom (positiveOpen X) 0
        ((perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
          (coefficientSupportedCone X K)) =
      (perfectSupportedWaldhausen (overlapOpen X).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen X).ι).obj
          (perfectOpenScalarCone (overlapOpen X).ι (nativePolynomialCoordinate X)
            (overlapLaurentUnit X)⁻¹ (polynomialCoordinate_overlap X)
            ((perfectRestrict (nativeMinus.app X).hom).obj K))) :=
  (KMap_kZeroObjectClass (perfectSupportedRestrict_exact
    (nativeMinus.app X).hom (positiveOpen X)) _).trans
      ((perfectSupportedWaldhausen (overlapOpen X).ι).kZeroObjectClass_iso
        (coefficientSupportedConeMinusIso X K))

/-- The original excision inverse recovers the actual global cone, without a chosen preimage. -/
theorem coefficientSupportedCone_excision (K : Perfect (nativeLineFunctor.obj X).obj) :
    (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
      (chart_cover X) 0).symm
        ((perfectSupportedWaldhausen (overlapOpen X).ι).kZeroObjectClass
          ((perfectAcyclicToSupported (overlapOpen X).ι).obj
            (perfectOpenScalarCone (overlapOpen X).ι (nativePolynomialCoordinate X)
              (overlapLaurentUnit X)⁻¹ (polynomialCoordinate_overlap X)
              ((perfectRestrict (nativeMinus.app X).hom).obj K)))) =
      (perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
        (coefficientSupportedCone X K) := by
  apply (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
    (chart_cover X) 0).injective
  rw [MulEquiv.apply_symm_apply]
  exact (coefficientSupportedCone_restrict_class X K).symm

variable [QuasiSeparatedSpace X.obj]

local instance positiveOpen_compactSpace : CompactSpace (positiveOpen X).toScheme :=
  isCompact_iff_compactSpace.mp (positiveOpen_isCompact X)

attribute [local instance] polynomial_quasiSeparated overlapOpen_compactSpace

local instance objectBoundaryOverlap_compactSpace :
    CompactSpace ((nativeMinus.app X).hom ⁻¹ᵁ positiveOpen X).toScheme :=
  overlapOpen_compactSpace X

/-- The original qcqs projective connecting map with its actual inverse overlap restriction. -/
def projectiveConnecting (n : ℕ) :
    PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) →*
      PerfectK (nativeLineFunctor.obj X).obj n :=
  (PerfectMayerVietoris.qcqsConnectingHom (nativeMinus.app X).hom (positiveOpen X)
    (positiveOpen_isCompact X) (chart_cover X) n).comp
      (laurentOverlapEquiv X (n + 1)).symm.toMonoidHom

/-- The original lower boundary of the forward unit is the inverse global coefficient cone. -/
theorem lowerBoundary_forward_coefficient (K : Perfect (nativeLineFunctor.obj X).obj) :
    PerfectMayerVietoris.lowerBoundary (nativeMinus.app X).hom (positiveOpen X)
        (chart_cover X) 0
        ((laurentOverlapEquiv X 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit X)
            ((perfectRestrict (Relative.minus.app X).hom).obj
              ((perfectRestrict (nativeMinus.app X).hom).obj K)))) =
      ((perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
        (coefficientSupportedCone X K))⁻¹ := by
  change (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
    (chart_cover X) 0).symm (qcqsPerfectConnectingHom (overlapOpen X).ι 0 _) = _
  rw [laurentOverlap_forward_coefficient_boundary, map_inv, coefficientSupportedCone_excision]

/-- Original support forgetting gives the actual projective boundary of the same forward unit. -/
theorem projectiveConnecting_forward_coefficient (K : Perfect (nativeLineFunctor.obj X).obj) :
    projectiveConnecting X 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit X)
          ((perfectRestrict (Relative.minus.app X).hom).obj
            ((perfectRestrict (nativeMinus.app X).hom).obj K))) =
      (perfectSupportedKMap (positiveOpen X).ι 0
        ((perfectSupportedWaldhausen (positiveOpen X).ι).kZeroObjectClass
          (coefficientSupportedCone X K)))⁻¹ :=
  (congrArg (perfectSupportedKMap (positiveOpen X).ι 0)
    (lowerBoundary_forward_coefficient X K)).trans
      (map_inv (perfectSupportedKMap (positiveOpen X).ι 0) _)

/-- The original forward unit has the original Phi pair on every base perfect object. -/
theorem projectiveConnecting_forward_coefficient_phi (K : Perfect X.obj) :
    projectiveConnecting X 0
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit X)
          ((perfectRestrict (Relative.minus.app X).hom).obj
            ((perfectRestrict (nativeMinus.app X).hom).obj
              ((nativeFirstSummand X).obj K)))) =
      nativeTwoSummandKMap X 0
        (((perfectWaldhausen X.obj).kZeroObjectClass K)⁻¹,
          (perfectWaldhausen X.obj).kZeroObjectClass K) := by
  rw [projectiveConnecting_forward_coefficient, coefficientSupportedCone_forget_phi,
    ← map_inv]
  simp only [Prod.inv_mk, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
