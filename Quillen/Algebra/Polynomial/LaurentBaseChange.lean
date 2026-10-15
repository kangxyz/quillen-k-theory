/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PolynomialBaseChange
export CommRingCat.PolynomialLaurent
  (coefficient coordinateUnit invert_naturality laurentCoefficient laurentMap laurentMap_C
  laurentMap_T laurentMap_comp laurent_hom_ext laurent_isPushout laurent_square minus_naturality
  polynomialMap polynomialMap_comp polynomial_isPushout polynomial_square toLaurent_naturality)
end Quillen.PolynomialBaseChange

end
