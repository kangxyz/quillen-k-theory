/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Noetherian

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.ClosedImmersion.General
export AlgebraicGeometry.Scheme
  (closedSource_isLocallyNoetherian closedSource_isNoetherian)
end Quillen.CoherentScheme.ClosedImmersion.General

end
