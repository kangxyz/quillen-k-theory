/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone
public import Quillen.Waldhausen.SplitComplexes.FactorizationSign

/-! # Original scalar, Laurent restriction and supported cone consumers -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes.Affine AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.Fibration
universe u
namespace QuillenTest.PolynomialScalarCone

open Quillen

/-- The exact global coordinate becomes the original Laurent unit. -/
theorem original_coordinate (R : CommRingCat.{u}) :
    (laurentPlus R).appTop (polynomialGlobalCoordinate R) = ↑(laurentGlobalUnit R) :=
  polynomialGlobalCoordinate_laurentPlus R

/-- Actual restriction sends the original chain map to the existing Laurent automorphism. -/
theorem original_restricted_chain_map (R : CommRingCat.{u})
    (K : Complex (Spec (.of (Polynomial R)))) :
    (restrict (laurentPlus R)).map
      ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K) =
    (complexGlobalUnitIso _ (laurentGlobalUnit R)).hom.app
      ((restrict (laurentPlus R)).obj K) :=
  restrict_map_complexGlobalScalar_unit (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- The original scalar is weak for the actual relative-open model. -/
theorem original_relative_weakness (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (perfectOpenWeakWaldhausen (laurentPlus R)).weq
      ((perfectGlobalScalar _ (polynomialGlobalCoordinate R)).app K) :=
  perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- The supported object has the original mapping-cone complex. -/
theorem original_cone (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (polynomialScalarCone R K).obj.obj =
      CochainComplex.mappingCone ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
        K.obj) := polynomialScalarCone_original R K

/-- The actual canonical fiber keeps separate path and object-loop parameters. -/
theorem original_fiber_path (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) (t s : unitInterval) :
    (polynomialScalarConeFiberLoop R K t).val.2 s =
      acyclicNullhomotopy (perfectOpenNested (laurentPlus R))
        (s, (acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectLoop
          (polynomialScalarCone R K) t) := polynomialScalarConeFiberLoop_path R K t s

/-- The original coarse transformation cylinder retains both independent parameters. -/
theorem original_scalar_track (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) (s t : unitInterval) :
    perfectOpenScalarTrack (laurentPlus R) (polynomialGlobalCoordinate R)
      (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K (s, t) =
      weakNaturalTransformationRealizationHomotopy
        (perfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectOpenWeakWaldhausen (laurentPlus R))
        (changeWeak_exact (perfectOpenNested (laurentPlus R)))
        (changeWeak_exact (perfectOpenNested (laurentPlus R)))
        (perfectGlobalScalar _ (polynomialGlobalCoordinate R))
        (perfectGlobalScalar_openWeak (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R))
        (s, (perfectWaldhausen (Spec (.of (Polynomial R)))).kZeroObjectLoop K t) :=
  perfectOpenScalarTrack_apply _ _ _ _ K s t

/-- The literal cylinder-factorization quotient is transported by the displayed sign iso. -/
theorem original_signed_quotient (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (SplitFactorization.quotientToConeSequence
      ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj)).ShortExact :=
  SplitFactorization.quotientToConeSequence_shortExact _

/-- The cone sign transport leaves the original target inclusion unchanged. -/
theorem original_signed_target (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    CochainComplex.mappingCone.inr
        (-((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj)) ≫
      (Quillen.CochainComplex.mappingConeNegIso
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj)).hom =
      CochainComplex.mappingCone.inr
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj) :=
  Quillen.CochainComplex.mappingConeNegIso_inr _

end QuillenTest.PolynomialScalarCone
