/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleForwardQuotient
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNativeUnitOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionUnitNaturality

/-!
# The native double Laurent representative of the positive Bass comparison

The two original coefficient operations are transported through the composite
of the actual Laurent-fiber isomorphism and its actual product pullback.
This identifies the twice-positive comparison with the literal native double
unit followed by that unchanged transport and the two original quotients.
The Laurent isomorphisms are retained explicitly throughout.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
open Quillen.PerfectComplexes.ProductUnitInterchange
universe u v
namespace Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
attribute [local instance] Waldhausen.Additivity.KCommGroup

private theorem additiveOfHom_comp {A B C : Type v}
    [CommGroup A] [CommGroup B] [CommGroup C] (f : A →* B) (g : B →* C) :
    (AddCommGrpCat.ofHom f.toAdditive :
      AddCommGrpCat.of (Additive A) ⟶ AddCommGrpCat.of (Additive B)) ≫
      AddCommGrpCat.ofHom g.toAdditive = AddCommGrpCat.ofHom (g.comp f).toAdditive := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
local notation "ℒ" => baseProductFunctor
  (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
    (CommRingCat.of (ULift ℤ)))
local notation "ℓ" => AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
  (CommRingCat.of (ULift ℤ))
local notation "t" => AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit
  (CommRingCat.of (ULift ℤ))

/-- The actual twice-iterated coefficient/product comparison, preserving both original legs. -/
def doubleLaurentIso :
    space (op P, (laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≅
      (ℒ).obj ((ℒ).obj (space (op P, a))) :=
  laurentIso P ((laurentUnderFunctor R).obj a) ≪≫ (ℒ).mapIso (laurentIso P a)

/-- The double comparison keeps its specified two original geometric maps. -/
@[simp] theorem doubleLaurentIso_hom :
    (doubleLaurentIso P a).hom =
      (laurentIso P ((laurentUnderFunctor R).obj a)).hom ≫
        (ℒ).map (laurentIso P a).hom := rfl

variable [CompactSpace P.left]

/-- The existing single native comparison retains exactly the raw projection-unit operation. -/
theorem singleForwardUnit_native (n : ℕ) :
    (boundedFlatPerfectKPullback (laurentIso P a).hom (n + 1)).comp
      (projectionUnitOperation ℓ (space (op P, a)) t n) =
        boundedFlatCoefficientLaurentKOperation P a n :=
  boundedFlatCoefficientLaurentKOperation_native P a n

/-- Two actual coefficient operations are the native double operation through both Laurent isos. -/
theorem doubleForwardUnit_native (n : ℕ) :
    (boundedFlatPerfectKPullback (doubleLaurentIso P a).hom (n + 2)).comp
        (doubleProjectionUnitOperation ℓ ℓ (space (op P, a)) t t n) =
      (boundedFlatCoefficientLaurentKOperation P ((laurentUnderFunctor R).obj a)
        (n + 1)).comp (boundedFlatCoefficientLaurentKOperation P a n) := by
  rw [doubleLaurentIso_hom, boundedFlatPerfectKPullback_comp]
  unfold doubleProjectionUnitOperation
  change ((boundedFlatPerfectKPullback
      (laurentIso P ((laurentUnderFunctor R).obj a)).hom (n + 2)).comp
    ((boundedFlatPerfectKPullback ((ℒ).map (laurentIso P a).hom) (n + 2)).comp
      (projectionUnitOperation ℓ ((ℒ).obj (space (op P, a))) t (n + 1)))).comp
        (projectionUnitOperation ℓ (space (op P, a)) t n) = _
  rw [projectionUnitOperation_naturality]
  change ((boundedFlatPerfectKPullback
      (laurentIso P ((laurentUnderFunctor R).obj a)).hom (n + 2)).comp
        (projectionUnitOperation ℓ (space (op P, (laurentUnderFunctor R).obj a)) t (n + 1))).comp
      ((boundedFlatPerfectKPullback (laurentIso P a).hom (n + 1)).comp
        (projectionUnitOperation ℓ (space (op P, a)) t n)) = _
  rw [singleForwardUnit_native, singleForwardUnit_native]

/-- The original double representative agrees pointwise with its actual native transport. -/
theorem doubleForwardUnit_native_apply (b : BoundedFlatPerfectK (space (op P, a)) 0) :
    boundedFlatCoefficientLaurentKOperation P ((laurentUnderFunctor R).obj a) 1
      (boundedFlatCoefficientLaurentKOperation P a 0 b) =
    boundedFlatPerfectKPullback (doubleLaurentIso P a).hom 2
      (doubleProjectionUnitOperation ℓ ℓ (space (op P, a)) t t 0 b) :=
  (DFunLike.congr_fun (doubleForwardUnit_native P a 0) b).symm

/-- The additive K-zero representative is the literal native double-unit map with its real iso. -/
theorem doubleForwardUnitMap_native :
    boundedFlatCoefficientDoubleForwardUnitMap P a 0 =
      doubleLaurentUnitMap (space (op P, a)) ≫
        (boundedFlatPerfectKAddFunctor 2).map (doubleLaurentIso P a).hom.op := by
  dsimp only [boundedFlatCoefficientDoubleForwardUnitMap,
    boundedFlatCoefficientForwardUnitSection, doubleLaurentUnitMap,
    boundedFlatPerfectKAddFunctor]
  rw [additiveOfHom_comp, additiveOfHom_comp]
  erw [← doubleForwardUnit_native P a 0]
  simp only [Quiver.Hom.unop_op]

/-- The original twice-positive Bass map retains the native double unit and both quotient maps. -/
theorem doubleForwardUnitQuotient_native :
    (boundedFlatCoefficientDoubleForwardUnitQuotient P 0).app a =
      doubleLaurentUnitMap (space (op P, a)) ≫
        (boundedFlatPerfectKAddFunctor 2).map (doubleLaurentIso P a).hom.op ≫
          doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
            (boundedFlatCoefficientKAddFunctor P 2) a := by
  rw [boundedFlatCoefficientDoubleForwardUnitQuotient_representative,
    doubleForwardUnitMap_native, Category.assoc]

end Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
