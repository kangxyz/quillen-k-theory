/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Localization.Exactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.ModuleLocalization
export ModuleCat
  (isLocalizedModule_piMap shortComplex_exact_of_isLocalized_span)
end Quillen.ModuleLocalization

end
