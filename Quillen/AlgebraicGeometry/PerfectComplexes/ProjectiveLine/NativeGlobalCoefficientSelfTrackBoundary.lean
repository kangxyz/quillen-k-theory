/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarConeKMapComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackGlobalBoundary
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOverlapUnitOperation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientConeRestriction

/-! # Original native coefficient boundaries in every connective degree

The actual inverse overlap restriction transports the original Laurent unit operation. The
polynomial scalar restricts to the inverse overlap unit, giving one inverse in the original
supported boundary. The literal cone-map comparison and original support excision retain the
native coefficient cone and support-forgetting maps on every original input class.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme

variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj]

attribute [local instance] polynomial_quasiSeparated overlapOpen_compactSpace

local instance globalBoundaryOverlap_compactSpace :
    CompactSpace ((nativeMinus.app X).hom ⁻¹ᵁ positiveOpen X).toScheme :=
  overlapOpen_compactSpace X

attribute [local instance] Waldhausen.Additivity.KCommGroup


/-- Actual overlap restriction and support excision give the inverse native cone on all inputs. -/
theorem lowerBoundary_comp_selfTrack_coefficient_allDegrees
    (n : ℕ) :
    (PerfectMayerVietoris.lowerBoundary (nativeMinus.app X).hom (positiveOpen X)
        (chart_cover X) n).comp
      ((laurentOverlapEquiv X (n + 1)).symm.toMonoidHom.comp
        ((originalKSelfTrackOperation
          (perfectWaldhausen (polynomialFunctor.obj X).obj)
          (perfectWaldhausen (laurentFunctor.obj X).obj)
          (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n).comp
            (perfectKRestrict (nativeMinus.app X).hom n))) =
      invMonoidHom.comp (coefficientConeKMap X n) := by
  apply MonoidHom.ext
  intro a
  apply (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
    (chart_cover X) n).injective
  change (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
    (chart_cover X) n)
      ((perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
        (chart_cover X) n).symm
          (qcqsPerfectConnectingHom (overlapOpen X).ι n
            ((laurentOverlapEquiv X (n + 1)).symm
              (originalKSelfTrackOperation _ _
                (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n
                  (perfectKRestrict (nativeMinus.app X).hom n a))))) =
    (perfectSupportedExcisionKEquiv (nativeMinus.app X).hom (positiveOpen X)
      (chart_cover X) n) ((coefficientConeKMap X n a)⁻¹)
  rw [MulEquiv.apply_symm_apply, map_inv]
  change qcqsPerfectConnectingHom (overlapOpen X).ι n
      ((laurentOverlapEquiv X (n + 1)).symm
        (originalKSelfTrackOperation _ _
          (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n
            (perfectKRestrict (nativeMinus.app X).hom n a))) =
    (perfectSupportedKRestrict (nativeMinus.app X).hom (positiveOpen X) n
      (coefficientConeKMap X n a))⁻¹
  rw [laurentOverlap_unitSelfTrack_inverse, map_inv,
    qcqsPerfectConnectingHom_scalarUnitSelfTrack (overlapOpen X).ι
      (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
      (polynomialCoordinate_overlap X),
    perfectAcyclicSupportedKEquiv_scalarConeKMap]
  exact congrArg Inv.inv
    (DFunLike.congr_fun (coefficientConeKMap_restrict X n) a).symm

/-- Every original class retains the same negative chart, overlap transport and supported cone. -/
theorem lowerBoundary_selfTrack_coefficient_allDegrees
    (n : ℕ) (a : PerfectK (nativeLineFunctor.obj X).obj n) :
    PerfectMayerVietoris.lowerBoundary (nativeMinus.app X).hom (positiveOpen X)
      (chart_cover X) n ((laurentOverlapEquiv X (n + 1)).symm
        (originalKSelfTrackOperation
          (perfectWaldhausen (polynomialFunctor.obj X).obj)
          (perfectWaldhausen (laurentFunctor.obj X).obj)
          (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n
            (perfectKRestrict (nativeMinus.app X).hom n a))) =
      (coefficientConeKMap X n a)⁻¹ :=
  DFunLike.congr_fun (lowerBoundary_comp_selfTrack_coefficient_allDegrees X n) a

/-- The original projective boundary is the support-forgotten inverse native coefficient cone. -/
theorem projectiveConnecting_comp_selfTrack_coefficient_allDegrees
    (n : ℕ) :
    (projectiveConnecting X n).comp
      ((originalKSelfTrackOperation
        (perfectWaldhausen (polynomialFunctor.obj X).obj)
        (perfectWaldhausen (laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n).comp
          (perfectKRestrict (nativeMinus.app X).hom n)) =
      invMonoidHom.comp ((perfectSupportedKMap (positiveOpen X).ι n).comp
        (coefficientConeKMap X n)) := by
  apply MonoidHom.ext
  intro a
  have h := lowerBoundary_selfTrack_coefficient_allDegrees X n a
  exact (congrArg (perfectSupportedKMap (positiveOpen X).ι n) h).trans
    (map_inv (perfectSupportedKMap (positiveOpen X).ι n) _)

/-- The all-degree projective formula uses arbitrary original inputs, including K-zero. -/
theorem projectiveConnecting_selfTrack_coefficient_allDegrees
    (n : ℕ) (a : PerfectK (nativeLineFunctor.obj X).obj n) :
    projectiveConnecting X n
      (originalKSelfTrackOperation
        (perfectWaldhausen (polynomialFunctor.obj X).obj)
        (perfectWaldhausen (laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (minus.app X).hom (laurentGlobalUnit X)) n
          (perfectKRestrict (nativeMinus.app X).hom n a)) =
      (perfectSupportedKMap (positiveOpen X).ι n
        (coefficientConeKMap X n a))⁻¹ :=
  DFunLike.congr_fun (projectiveConnecting_comp_selfTrack_coefficient_allDegrees X n) a

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
