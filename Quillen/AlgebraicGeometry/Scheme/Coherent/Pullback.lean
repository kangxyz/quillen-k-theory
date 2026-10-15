/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineLocallyFiniteType_pullback)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (coherentPullback coherentPullbackCompIso coherentPullbackIdIso coherentPullback_additive
  coherentPullback_comp_inclusion coherentRestrictionIsoPullback)
end Quillen.CoherentScheme

namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (finitePresentation_pullback presentationOverToRestrict presentationOverToRestrict_isFinite
  presentationPullbackRestrict presentationPullbackRestrict_isFinite presentationRestrictToOver
  presentationRestrictToOver_isFinite quasicoherentDataPullback
  quasicoherentDataPullback_isFinitePresentation quasicoherent_pullback)
end Quillen.SchemeSheaf

end
