/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.PolynomialLaurentSchemeNaturality

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.CoefficientBaseChange
export AlgebraicGeometry.Scheme.BaseChange.Coefficients
  (laurentIso_schemeMap laurentMinus_schemeMap laurentPlus_schemeMap laurentProjection_schemeMap
  polynomialIso_schemeMap polynomialProjection_schemeMap schemeMap_coefficientMap)
end Quillen.Scheme.CoefficientBaseChange

end
