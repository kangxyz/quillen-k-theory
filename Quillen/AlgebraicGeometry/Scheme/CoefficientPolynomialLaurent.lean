/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.PolynomialLaurent

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.CoefficientBaseChange
export AlgebraicGeometry.Scheme.BaseChange.Coefficients
  (coefficientMap coefficientMap_coefficientProjection coefficientMap_comp
  coefficientMap_isPullback laurentIso laurentIso_globalUnit laurentIso_hom_fst
  laurentIso_hom_snd laurentMinus laurentMinus_projection laurentPlus laurentPlus_projection
  laurentProjection laurentSquare laurent_isPullback polynomialIso polynomialIso_hom_fst
  polynomialIso_hom_snd polynomialLaurentIso_minus polynomialLaurentIso_plus
  polynomialProjection polynomial_isPullback)
end Quillen.Scheme.CoefficientBaseChange

end
