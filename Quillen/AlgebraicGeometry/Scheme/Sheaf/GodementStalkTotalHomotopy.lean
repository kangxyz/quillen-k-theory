/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.TotalHomotopy

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (godementStalkBackDEntry godementStalkBackDEntry_congr godementStalkBackDEntry_congr_middle
  godementStalkBackEntry godementStalkBackEntry_congr godementStalkDBackEntry
  godementStalkDBackEntry_congr_middle godementStalkTotalHomotopy
  godementStalkTotalHomotopyEquiv godementStalkTotalUnit_quasiIso godementStalkTotal_contraction
  godementStalkTotal_sign_cancel godementStalkTotal_sign_square)
end Quillen.SchemeSheaf

end
