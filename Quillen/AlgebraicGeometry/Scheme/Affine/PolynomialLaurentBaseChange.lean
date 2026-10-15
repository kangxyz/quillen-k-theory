/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.BaseChange

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.Bass
export AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
  (integerMap integerMap_naturality laurentSpecIso laurentSpecIso_hom_fst laurentSpecIso_hom_snd
  laurentSpecIso_naturality laurentSpec_isPullback polynomialLaurentSpecIso_minus
  polynomialLaurentSpecIso_plus polynomialSpecIso polynomialSpecIso_hom_fst
  polynomialSpecIso_hom_snd polynomialSpecIso_naturality polynomialSpec_isPullback
  spec_integerMap)
end Quillen.Scheme.Bass

end
