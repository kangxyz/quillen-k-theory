/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.TotalMatrix

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (godementSourceStalk godementStalkHorizontal godementStalkHorizontal_back
  godementStalkIntTerm_isZero_negative godementStalkTotalBack godementStalkTotalCocone
  godementStalkTotalDesc godementStalkTotalDiagram godementStalkTotalIn
  godementStalkTotalIn_back godementStalkTotalIn_d godementStalkTotalIn_d_to
  godementStalkTotalIn_desc godementStalkTotalIn_projection_ne
  godementStalkTotalIn_projection_zero godementStalkTotalIsColimit godementStalkTotalProjection
  godementStalkTotalProjection_comm godementStalkTotalRetraction godementStalkTotalUnit
  godementStalkTotalUnit_f godementStalkTotalUnit_projection godementStalkTotalUnit_retraction
  godementStalkTotal_hom_ext godementTotalStalk)
end Quillen.SchemeSheaf

end
