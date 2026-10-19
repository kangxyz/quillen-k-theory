/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedGlobalUnitIdentityOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPairUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapOuterUnit
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OpenPairInterchange
public import Quillen.Waldhausen.SConstruction.Iterated.IdentityActionInterchangeSign

/-!
# Original supported unit interchange and genuine pair-factor preservation

Two original supported scalar operations anticommute in every nonnegative
degree, including original K-zero. The actual independent-factor swap preserves
both arbitrary scalar units on the original strict supported pair Models.
The normalized identity endpoint is retained in the comparison used here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.Bass
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.ProductSwapUnit
open Quillen.PerfectComplexes.SupportedGlobalUnitIdentityOperation
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedProductUnitInterchange

/-- The actual supported scalar identity actions anticommute on every original K-group. -/
theorem unitKOperation_interchange_sign {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r s : (Γ(X, ⊤))ˣ) (n : ℕ) (a : BoundedFlatPerfectSupportedK j n) :
    unitKOperation j s (n + 1) (unitKOperation j r n a) =
      (unitKOperation j r (n + 1) (unitKOperation j s n a))⁻¹ :=
  originalKIdentityAction_interchange_sign (boundedFlatPerfectSupportedWaldhausen j)
    (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)
    (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j s) n a

/-- The unchanged original chosen-zero-rebased supported tracks have the same signed interchange. -/
theorem originalUnit_interchange_sign {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r s : (Γ(X, ⊤))ˣ) (n : ℕ) (a : BoundedFlatPerfectSupportedK j n) :
    originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
      (boundedFlatPerfectSupportedWaldhausen j) (boundedFlatPerfectSupportedGlobalUnitHomotopy j s)
      (n + 1)
      (originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
        (boundedFlatPerfectSupportedWaldhausen j)
        (boundedFlatPerfectSupportedGlobalUnitHomotopy j r)
        n a) =
      (originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
        (boundedFlatPerfectSupportedWaldhausen j)
        (boundedFlatPerfectSupportedGlobalUnitHomotopy j r)
        (n + 1)
        (originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
          (boundedFlatPerfectSupportedWaldhausen j)
          (boundedFlatPerfectSupportedGlobalUnitHomotopy j s) n a))⁻¹ := by
  simp only [originalUnit_operation]
  exact unitKOperation_interchange_sign j r s n a

variable {S T : Scheme.{u}} (p : S ⟶ integerBase) (q : T ⟶ integerBase)
  [QuasiCompact p] [QuasiCompact q]

/-- The genuine product swap as an arrow of the original open-pair category. -/
def swapPairMap (A : Scheme.QuasiCompactOpenPairs.{u}) :
    ((pairBaseProductFunctor q).obj ((pairBaseProductFunctor p).obj A)).obj ⟶
      ((pairBaseProductFunctor p).obj ((pairBaseProductFunctor q).obj A)).obj :=
  ((pairBaseProductSwapIso p q).hom.app A).hom

/-- The strict supported pair swap preserves the first factor's actual global scalar. -/
theorem strictSwap_preserves_inner (A : Scheme.QuasiCompactOpenPairs.{u}) (r : (Γ(S, ⊤))ˣ) :
    Preserves (GlobalSectionChangeIndex.supportedPairModelMap (swapPairMap p q A)).functor
      (SupportedTensorEvaluation.unit
        (X := Opposite.op (((pairBaseProductFunctor p).obj
          ((pairBaseProductFunctor q).obj A)).obj.obj.right))
        (((pairBaseProductFunctor p).obj ((pairBaseProductFunctor q).obj A)).obj.obj.hom)
        (outerUnit p q A.obj.obj.right r))
      (SupportedTensorEvaluation.unit
        (X := Opposite.op (((pairBaseProductFunctor q).obj
          ((pairBaseProductFunctor p).obj A)).obj.obj.right))
        (((pairBaseProductFunctor q).obj ((pairBaseProductFunctor p).obj A)).obj.obj.hom)
        (innerUnit p q A.obj.obj.right r)) :=
  SupportedPairUnit.pairMap_preserves_of_eq (swapPairMap p q A) _ _
    (swap_unit p q A.obj.obj.right r)

/-- The same strict supported pair swap preserves the second independent factor's scalar. -/
theorem strictSwap_preserves_outer (A : Scheme.QuasiCompactOpenPairs.{u}) (s : (Γ(T, ⊤))ˣ) :
    Preserves (GlobalSectionChangeIndex.supportedPairModelMap (swapPairMap p q A)).functor
      (SupportedTensorEvaluation.unit
        (X := Opposite.op (((pairBaseProductFunctor p).obj
          ((pairBaseProductFunctor q).obj A)).obj.obj.right))
        (((pairBaseProductFunctor p).obj ((pairBaseProductFunctor q).obj A)).obj.obj.hom)
        (innerUnit q p A.obj.obj.right s))
      (SupportedTensorEvaluation.unit
        (X := Opposite.op (((pairBaseProductFunctor q).obj
          ((pairBaseProductFunctor p).obj A)).obj.obj.right))
        (((pairBaseProductFunctor q).obj ((pairBaseProductFunctor p).obj A)).obj.obj.hom)
        (outerUnit q p A.obj.obj.right s)) :=
  SupportedPairUnit.pairMap_preserves_of_eq (swapPairMap p q A) _ _
    (ProductSwapOuterUnit.swap_outer_unit p q A.obj.obj.right s)

/-- The original supported bounded-flat pair pullback preserves the first factor's scalar. -/
theorem nativeSwap_preserves_inner (A : Scheme.QuasiCompactOpenPairs.{u}) (r : (Γ(S, ⊤))ˣ) :
    Preserves (boundedFlatPerfectSupportedPullback (swapPairMap p q A))
      (boundedFlatPerfectSupportedGlobalUnitIso
        (((pairBaseProductFunctor p).obj ((pairBaseProductFunctor q).obj A)).obj.obj.hom)
        (outerUnit p q A.obj.obj.right r))
      (boundedFlatPerfectSupportedGlobalUnitIso
        (((pairBaseProductFunctor q).obj ((pairBaseProductFunctor p).obj A)).obj.obj.hom)
        (innerUnit p q A.obj.obj.right r)) :=
  pullback_preserves_of_eq (swapPairMap p q A) _ _ (swap_unit p q A.obj.obj.right r)

/-- The same original supported pullback preserves the second independent scalar. -/
theorem nativeSwap_preserves_outer (A : Scheme.QuasiCompactOpenPairs.{u}) (s : (Γ(T, ⊤))ˣ) :
    Preserves (boundedFlatPerfectSupportedPullback (swapPairMap p q A))
      (boundedFlatPerfectSupportedGlobalUnitIso
        (((pairBaseProductFunctor p).obj ((pairBaseProductFunctor q).obj A)).obj.obj.hom)
        (innerUnit q p A.obj.obj.right s))
      (boundedFlatPerfectSupportedGlobalUnitIso
        (((pairBaseProductFunctor q).obj ((pairBaseProductFunctor p).obj A)).obj.obj.hom)
        (outerUnit q p A.obj.obj.right s)) :=
  pullback_preserves_of_eq (swapPairMap p q A) _ _
    (ProductSwapOuterUnit.swap_outer_unit p q A.obj.obj.right s)

end Quillen.PerfectComplexes.SupportedProductUnitInterchange
