/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PolynomialBaseChange
export CommRingCat.PolynomialLaurent
  (laurentUnderCoefficient laurentUnderFunctor laurentUnderSquare laurentUnderSquareFunctor
  laurentUnderSquareMap laurentUnderSquare_forget polynomialUnderCoefficient
  polynomialUnderCoefficient_toLaurent polynomialUnderCoefficient_toLaurentInvert
  polynomialUnderFunctor underToLaurent underToLaurentInvert)
end Quillen.PolynomialBaseChange

end
