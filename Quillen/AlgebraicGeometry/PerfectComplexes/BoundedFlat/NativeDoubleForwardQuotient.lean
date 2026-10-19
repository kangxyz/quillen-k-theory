/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleNativeUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleQuotientTransport
public import Quillen.KTheory.Bass.SchemeDoubleContractionSwap

/-!
# The native twice-positive Bass comparison

The literal native double unit followed by the two original Bass projections
is natural on all quasi-compact schemes. Its value is invertible on each
quasi-separated scheme, by the actual coefficient-row comparison at the
identity algebra. The original double Laurent swap therefore acts by minus
the identity on the double contraction of the original K-two functor there.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
open Quillen.PerfectComplexes.ProductUnitInterchange
universe u
namespace Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
attribute [local instance] Waldhausen.Additivity.KCommGroup
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus
local notation "L" => PolynomialLaurent.Relative.laurentFunctor.op
local notation "ℓ" => PolynomialLaurent.laurentProjection
  (CommRingCat.of (ULift ℤ))
local notation "t" => PolynomialLaurent.laurentGlobalUnit
  (CommRingCat.of (ULift ℤ))
local notation "ℒ" => baseProductFunctor ℓ

private theorem additiveOfHom_comp {A B C : Type (u + 1)}
    [CommGroup A] [CommGroup B] [CommGroup C] (f : A →* B) (g : B →* C) :
    (AddCommGrpCat.ofHom f.toAdditive :
      AddCommGrpCat.of (Additive A) ⟶ AddCommGrpCat.of (Additive B)) ≫
      AddCommGrpCat.ofHom g.toAdditive = AddCommGrpCat.ofHom (g.comp f).toAdditive := rfl

/-- The unchanged original K-functor restricted to the actual quasi-compact schemes. -/
def quasiCompactKFunctor (n : ℕ) : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  quasiCompactSchemesInclusion.op ⋙ boundedFlatPerfectKAddFunctor n

/-- The two literal native projection-unit operations are natural before quotienting. -/
theorem doubleUnit_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (boundedFlatPerfectKPullback ((ℒ).map ((ℒ).map f)) (n + 2)).comp
        (doubleProjectionUnitOperation ℓ ℓ Y t t n) =
      (doubleProjectionUnitOperation ℓ ℓ X t t n).comp
        (boundedFlatPerfectKPullback f n) := by
  unfold doubleProjectionUnitOperation
  rw [← MonoidHom.comp_assoc, projectionUnitOperation_naturality,
    MonoidHom.comp_assoc, projectionUnitOperation_naturality, ← MonoidHom.comp_assoc]

/-- Naturality of the unchanged original double unit as an additive arrow on schemes. -/
theorem doubleLaurentUnitMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectKAddFunctor 0).map f.op ≫ doubleLaurentUnitMap X =
      doubleLaurentUnitMap Y ≫
        (boundedFlatPerfectKAddFunctor 2).map ((ℒ).map ((ℒ).map f)).op := by
  dsimp only [doubleLaurentUnitMap, boundedFlatPerfectKAddFunctor]
  rw [additiveOfHom_comp, additiveOfHom_comp]
  simp only [Quiver.Hom.unop_op]
  erw [doubleUnit_naturality f 0]

/-- The literal native K-zero to double-Laurent K-two operation on the all-qc domain. -/
def doubleUnitSection : quasiCompactKFunctor.{u} 0 ⟶ L ⋙ L ⋙ quasiCompactKFunctor 2 where
  app X := doubleLaurentUnitMap X.unop.obj
  naturality {X Y} f := by
    change (boundedFlatPerfectKAddFunctor 0).map f.unop.hom.op ≫
        doubleLaurentUnitMap Y.unop.obj =
      doubleLaurentUnitMap X.unop.obj ≫
        (boundedFlatPerfectKAddFunctor 2).map ((ℒ).map ((ℒ).map f.unop.hom)).op
    exact doubleLaurentUnitMap_naturality f.unop.hom

/-- The native twice-positive comparison uses the two unchanged original projections. -/
def doubleForwardQuotient :
    quasiCompactKFunctor.{u} 0 ⟶ contraction p m (contraction p m (quasiCompactKFunctor 2)) :=
  doubleUnitSection ≫
    { app X := doubleContractionπ p m (quasiCompactKFunctor 2) X
      naturality {_ _} f := doubleContractionπ_naturality p m (quasiCompactKFunctor 2) f }

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)

/-- The actual double quotient transport cancels precisely the retained double Laurent iso. -/
theorem doubleQuotient_native_transport :
    (boundedFlatPerfectKAddFunctor 2).map (doubleLaurentIso P a).hom.op ≫
        doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientKAddFunctor P 2) a ≫
        (boundedFlatCoefficientDoubleContractionTransportIso P
          (quasiCompactKFunctor 2)).hom.app a =
      doubleContractionπ p m (quasiCompactKFunctor 2)
        ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  have h := boundedFlatCoefficientDoubleContractionTransportIso_π P
    (quasiCompactKFunctor 2) a
  change doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P 2) a ≫
      (boundedFlatCoefficientDoubleContractionTransportIso P
        (quasiCompactKFunctor 2)).hom.app a =
    (boundedFlatPerfectKAddFunctor 2).map (doubleLaurentIso P a).inv.op ≫ _ at h
  rw [h, ← Category.assoc, ← Functor.map_comp]
  simp only [← op_comp, Iso.inv_hom_id, op_id]
  erw [(boundedFlatPerfectKAddFunctor 2).map_id]
  exact Category.id_comp _

/-- The actual coefficient isomorphism represents the native map through the actual quotients. -/
theorem doubleForwardQuotient_coefficient :
    (boundedFlatCoefficientDoubleForwardUnitQuotient P 0).app a ≫
        (boundedFlatCoefficientDoubleContractionTransportIso P
          (quasiCompactKFunctor 2)).hom.app a =
      doubleForwardQuotient.app ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  rw [doubleForwardUnitQuotient_native]
  simp only [Category.assoc]
  rw [doubleQuotient_native_transport]
  rfl

/-- Native invertibility at each actual coefficient fiber of a fixed QCQS base. -/
instance doubleForwardQuotient_coefficient_isIso [QuasiSeparatedSpace P.left] :
    IsIso (doubleForwardQuotient.app ((boundedFlatCoefficientQuasiCompactRow P).obj a)) := by
  rw [← doubleForwardQuotient_coefficient P a]
  infer_instance

/-- Native invertibility is local to the given quasi-separated quasi-compact scheme. -/
instance doubleForwardQuotient_app_isIso (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] : IsIso (doubleForwardQuotient.app X) := by
  let P : Over (Spec PolynomialLaurent.Relative.integerRing) :=
    Over.mk (toIntegerBase X.unop.obj)
  let : CompactSpace P.left := inferInstanceAs (CompactSpace X.unop.obj)
  let : QuasiSeparatedSpace P.left := inferInstanceAs (QuasiSeparatedSpace X.unop.obj)
  let a : Under PolynomialLaurent.Relative.integerRing := Under.mk (𝟙 _)
  let e : (boundedFlatCoefficientQuasiCompactRow P).obj a ≅ X :=
    (quasiCompactSchemeProperty.isoMk (identityProjectionIso P)).symm.op
  exact (NatTrans.isIso_app_iff_of_iso doubleForwardQuotient e).mp inferInstance

/-- The actual native comparison intertwines the descended swap with its proved unit sign. -/
theorem doubleForwardQuotient_swap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleForwardQuotient.app X ≫
        PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X =
      -doubleForwardQuotient.app X := by
  change (doubleLaurentUnitMap X.unop.obj ≫ _) ≫ _ = -(_ ≫ _)
  rw [Category.assoc, PolynomialLaurent.Relative.doubleContractionπ_swap,
    ← Category.assoc]
  change (doubleLaurentUnitMap X.unop.obj ≫ (boundedFlatPerfectKAddFunctor 2).map
    (baseProductSwapMap ℓ ℓ X.unop.obj).op) ≫ _ = _
  rw [doubleLaurentUnitMap_swap, Preadditive.neg_comp]
  rfl

/-- The actual variable swap is minus the identity on the original double K-two quotient. -/
theorem doubleContractionSwap_KTwo_eq_neg_id (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X = -𝟙 _ := by
  apply (cancel_epi (doubleForwardQuotient.app X)).1
  rw [doubleForwardQuotient_swap, Preadditive.comp_neg, Category.comp_id]

end Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
