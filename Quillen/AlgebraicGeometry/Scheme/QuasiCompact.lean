/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.QuasiCompactCategory

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme
export AlgebraicGeometry.Scheme
  (QuasiCompactSchemes quasiCompactSchemeProperty quasiCompactSchemesInclusion
  quasiCompactSchemes_compactSpace)
end Quillen.Scheme

end
