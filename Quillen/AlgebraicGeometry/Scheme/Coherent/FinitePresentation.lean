/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineFiniteSheaf_exists_presentation affineLocallyFiniteType_finitePresentation)
export AlgebraicGeometry.Scheme.Modules
  (affinePresentationToOver affinePresentationToOver_isFinite exists_finite_presentation_tilde)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (coherentToFinitePresentation coherent_obj_finitePresentation coherent_obj_quasicoherent)
end Quillen.CoherentScheme

end
