/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.PolynomialLaurent
export AlgebraicGeometry.Scheme.PolynomialLaurent
  (instFlatLaurentMinus instFlatLaurentPlus instFlatLaurentProjection
  instFlatPolynomialProjection instIsOpenImmersionLaurentMinus instIsOpenImmersionLaurentPlus
  laurentCoordinateUnit laurentGlobalUnit laurentGlobalUnit_original_T laurentMinus
  laurentMinus_opensRange laurentMinus_projection laurentPlus laurentPlus_opensRange
  laurentPlus_projection laurentProjection polynomialProjection)
end Quillen.Scheme.PolynomialLaurent

end
