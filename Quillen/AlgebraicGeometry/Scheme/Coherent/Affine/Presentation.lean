/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineCoherentToFinitePresentation affineCoherent_finitePresentation)
export AlgebraicGeometry.Scheme.Modules
  (finitePresentation_tilde)
end Quillen.CoherentScheme

end
