/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Map

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleTensorStalkHom moduleTensorStalkHom_germ moduleTensorToPoint moduleTensorToPointApp
  moduleTensorToPointPresheaf moduleTensorToPoint_section schemeModule_germ_smul)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
abbrev originalModuleTensorPresheaf := @AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf
end Quillen.SchemeSheaf

end
