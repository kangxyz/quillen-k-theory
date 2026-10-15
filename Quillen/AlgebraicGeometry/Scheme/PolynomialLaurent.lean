/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Relative

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.Bass
export AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
  (instFlatLaurentProjection instFlatPolynomialProjection instIsOpenImmersionMinus
  instIsOpenImmersionPlus integerRing laurentFunctor laurentProjection minus minus_projection
  plus plus_projection polynomialFunctor polynomialProjection)
end Quillen.Scheme.Bass

end
