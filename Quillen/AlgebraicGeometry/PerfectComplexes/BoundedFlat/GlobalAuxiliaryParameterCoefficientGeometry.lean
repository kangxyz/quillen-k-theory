/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportRestriction
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseCanonicalRow
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-!
# Actual auxiliary support opens on the integral coefficient row

The original fiber support is the projection preimage of the union of the auxiliary open
and the localization range. The canonical parameter-row symmetry preserves this open,
the original ambient support, and its inverse image on the localization open.
Only the original open-immersion assumption is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.Products
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original native intersection support is the preimage of the actual union. -/
theorem fiberSupportOpen_eq (a : Under R) :
    boundedFlatCoefficientFiberSupportOpen f T a =
      projection (op Q, a) ⁻¹ᵁ (T ⊔ f.left.opensRange) := by
  rw [boundedFlatCoefficientFiberSupportOpen, boundedFlatCoefficientSupportOpen,
    Scheme.Hom.preimage_sup]
  congr 1
  exact Scheme.Hom.opensRange_of_isPullback (schemeMap f a)
    (projection (op P, a)) (projection (op Q, a)) f.left (schemeMap_isPullback f a)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}

/-- The actual row isomorphism preserves every specified auxiliary support open. -/
theorem row_supportOpen (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (canonicalRowIso Q a).hom ⁻¹ᵁ
        (CategoryTheory.Limits.pullback.snd (toIntegerBase (Spec a.right))
          (toIntegerBase Q.left) ⁻¹ᵁ T) = boundedFlatCoefficientSupportOpen Q T a := by
  change ((canonicalRowIso Q a).hom ≫ CategoryTheory.Limits.pullback.snd _ _) ⁻¹ᵁ T = _
  rw [canonicalRowIso_snd]
  rfl

/-- The same full row transports the original union support, including the open range. -/
theorem row_fiberSupportOpen (f : P ⟶ Q) [IsOpenImmersion f.left]
    (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (canonicalRowIso Q a).hom ⁻¹ᵁ
        (CategoryTheory.Limits.pullback.snd (toIntegerBase (Spec a.right))
          (toIntegerBase Q.left) ⁻¹ᵁ (T ⊔ f.left.opensRange)) =
      boundedFlatCoefficientFiberSupportOpen f T a := by
  rw [row_supportOpen, fiberSupportOpen_eq]
  rfl

/-- The open-side row keeps the literal inverse image of the original auxiliary support. -/
theorem row_openSupportOpen (f : P ⟶ Q)
    (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (canonicalRowIso P a).hom ⁻¹ᵁ
        (CategoryTheory.Limits.pullback.snd (toIntegerBase (Spec a.right))
          (toIntegerBase P.left) ⁻¹ᵁ (f.left ⁻¹ᵁ T)) =
      boundedFlatCoefficientOpenSupportOpen f T a := by
  rw [row_supportOpen, boundedFlatCoefficientOpenSupportOpen_eq]
  rfl

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
