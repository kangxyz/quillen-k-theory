/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export ModuleCat
  (scalarExtensionTensorIso scalarExtensionTensorIso_hom_tmul scalarExtensionTensorIso_inv_tmul
  scalarExtensionTensorIso_naturality scalarExtensionTensorNatIso)
end Quillen.SchemeSheaf

end
