/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Limits.BiproductPushout

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen
/-- Historical name for the canonical Aglib declaration. -/
alias isPushout_biprod_map := CategoryTheory.Limits.IsPushout.biprod_map
end Quillen

end
