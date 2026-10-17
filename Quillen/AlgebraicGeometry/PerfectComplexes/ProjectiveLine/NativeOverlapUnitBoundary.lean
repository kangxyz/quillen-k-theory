/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeCoordinate
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassCharts
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarSupportedBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneRestriction

/-!
# The original native Laurent unit on the actual overlap

The native polynomial scalar restricts to the inverse of the actual Laurent unit. Original
overlap restriction and the original qcqs supported boundary therefore give the inverse scalar
cone class on every polynomial-chart perfect object, without an affine hypothesis on the base.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

variable (X : QuasiCompactSchemes.{u})

/-- The unchanged integral Laurent unit pulled back to the actual native product. -/
def laurentGlobalUnit : (Γ((Relative.laurentFunctor.obj X).obj, ⊤))ˣ :=
  Units.map (pullback.snd (toIntegerBase X.obj)
    (PolynomialLaurent.laurentProjection Relative.integerRing)).appTop.hom.toMonoidHom
      (PolynomialLaurent.laurentGlobalUnit Relative.integerRing)

/-- The actual native inverse-coordinate chart carries the scalar to the inverse unit. -/
theorem polynomialCoordinate_laurentMinus :
    (Relative.minus.app X).hom.appTop (nativePolynomialCoordinate X) =
      ↑((laurentGlobalUnit X)⁻¹) := by
  have hs : (Relative.minus.app X).hom ≫
        pullback.snd (toIntegerBase X.obj)
          (PolynomialLaurent.polynomialProjection Relative.integerRing) =
      pullback.snd (toIntegerBase X.obj)
          (PolynomialLaurent.laurentProjection Relative.integerRing) ≫
        PolynomialLaurent.laurentMinus Relative.integerRing := by
    simp [Relative.minus, qcBaseProductTransformation, baseProductTransformation]
  have h := congrArg (fun f => f.appTop) hs
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  have hr := ConcreteCategory.congr_hom h
    (PolynomialLaurent.polynomialGlobalCoordinate Relative.integerRing)
  change (Relative.minus.app X).hom.appTop (nativePolynomialCoordinate X) =
    (pullback.snd (toIntegerBase X.obj)
      (PolynomialLaurent.laurentProjection Relative.integerRing)).appTop
        ((PolynomialLaurent.laurentMinus Relative.integerRing).appTop
          (PolynomialLaurent.polynomialGlobalCoordinate Relative.integerRing)) at hr
  rw [PolynomialLaurent.polynomialGlobalCoordinate_laurentMinus] at hr
  exact hr

/-- Pull back the original Laurent unit through the original inverse overlap isomorphism. -/
def overlapLaurentUnit : (Γ((overlapOpen X).toScheme, ⊤))ˣ :=
  Units.map (overlapOpenIso X).inv.appTop.hom.toMonoidHom (laurentGlobalUnit X)

/-- The inverse actual overlap isomorphism preserves the original negative Laurent inclusion. -/
@[reassoc]
theorem overlapOpenIso_inv_minus :
    (overlapOpenIso X).inv ≫ (Relative.minus.app X).hom = (overlapOpen X).ι := by
  rw [← overlapOpenIso_hom_inclusion, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The negative native polynomial scalar restricts to the inverse actual overlap unit. -/
theorem polynomialCoordinate_overlap :
    (overlapOpen X).ι.appTop (nativePolynomialCoordinate X) =
      ↑((overlapLaurentUnit X)⁻¹) := by
  have h := congrArg (fun f => f.appTop) (overlapOpenIso_inv_minus X)
  rw [Scheme.Hom.comp_appTop] at h
  have hr := ConcreteCategory.congr_hom h (nativePolynomialCoordinate X)
  change (overlapOpenIso X).inv.appTop
      ((Relative.minus.app X).hom.appTop (nativePolynomialCoordinate X)) =
    (overlapOpen X).ι.appTop (nativePolynomialCoordinate X) at hr
  rw [polynomialCoordinate_laurentMinus] at hr
  exact hr.symm

/-- Nested original restriction identifies the same polynomial coefficient on the overlap. -/
def laurentOverlapCoefficientIso (K : Perfect (Relative.polynomialFunctor.obj X).obj) :
    (perfectRestrict (overlapOpenIso X).inv).obj
        ((perfectRestrict (Relative.minus.app X).hom).obj K) ≅
      (perfectRestrict (overlapOpen X).ι).obj K :=
  (locallyPerfect (overlapOpen X).toScheme).isoMk
    ((restrictCompIso (overlapOpenIso X).inv (Relative.minus.app X).hom).app K.obj ≪≫
      (eqToIso (restrict_congr (overlapOpenIso_inv_minus X))).app K.obj)

/-- Original overlap transport preserves the forward unit on the same restricted coefficient. -/
theorem laurentOverlapEquiv_symm_globalUnit_coefficient
    (K : Perfect (Relative.polynomialFunctor.obj X).obj) :
    (laurentOverlapEquiv X 1).symm
        (perfectGlobalUnitKOneClass _ (laurentGlobalUnit X)
          ((perfectRestrict (Relative.minus.app X).hom).obj K)) =
      perfectGlobalUnitKOneClass _ (overlapLaurentUnit X)
        ((perfectRestrict (overlapOpen X).ι).obj K) := by
  change perfectKRestrict (overlapOpenIso X).inv 1 _ = _
  rw [perfectGlobalUnitKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso _ _ (laurentOverlapCoefficientIso X K)

variable [QuasiSeparatedSpace X.obj]

local instance polynomial_quasiSeparated :
    QuasiSeparatedSpace (Relative.polynomialFunctor.obj X).obj :=
  QuasiSeparatedSpace.of_isOpenEmbedding (nativeMinus.app X).hom.isOpenEmbedding

local instance overlapOpen_compactSpace : CompactSpace (overlapOpen X).toScheme :=
  isCompact_iff_compactSpace.mp
    ((nativeMinus.app X).hom.isCompact_preimage (positiveOpen_isCompact X))

/-- The actual forward Laurent unit has the inverse scalar-cone class as its original boundary.
-/
theorem laurentOverlap_forward_coefficient_boundary
    (K : Perfect (Relative.polynomialFunctor.obj X).obj) :
    qcqsPerfectConnectingHom (overlapOpen X).ι 0
        ((laurentOverlapEquiv X 1).symm
          (perfectGlobalUnitKOneClass _ (laurentGlobalUnit X)
            ((perfectRestrict (Relative.minus.app X).hom).obj K))) =
      ((perfectSupportedWaldhausen (overlapOpen X).ι).kZeroObjectClass
        ((perfectAcyclicToSupported (overlapOpen X).ι).obj
          (perfectOpenScalarCone (overlapOpen X).ι (nativePolynomialCoordinate X)
            (overlapLaurentUnit X)⁻¹ (polynomialCoordinate_overlap X) K)))⁻¹ := by
  rw [laurentOverlapEquiv_symm_globalUnit_coefficient]
  exact qcqsPerfectConnectingHom_globalUnit_inverse_scalar (overlapOpen X).ι K
    (nativePolynomialCoordinate X) (overlapLaurentUnit X) (polynomialCoordinate_overlap X)

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
