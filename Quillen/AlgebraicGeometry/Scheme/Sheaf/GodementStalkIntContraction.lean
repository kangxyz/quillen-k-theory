/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.IntContraction

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (godementIntGerm_XIso godementStalkIntBack godementStalkIntBack_cast
  godementStalkIntBack_negative godementStalkIntContraction_succ
  godementStalkIntContraction_zero godementStalkIntD godementStalkIntD_cast
  godementStalkIntD_cast_succ godementStalkIntGerm godementStalkIntGerm_retraction
  godementStalkIntRetraction godementStalkIntTerm godementStalkIntTermIso)
end Quillen.SchemeSheaf

end
