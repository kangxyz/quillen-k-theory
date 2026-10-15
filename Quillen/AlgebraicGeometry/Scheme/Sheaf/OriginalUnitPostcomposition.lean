/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PlusQuasiIso
public import Aglib.CategoryTheory.NatTrans.Unit

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
abbrev originalNaturalUnitPostcompose := @CategoryTheory.NatTrans.unitPostcompose
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
abbrev originalNaturalUnitPrecompose := @CategoryTheory.NatTrans.unitPrecompose
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalNaturalUnitPrecompose_quasiIso :=
  AlgebraicGeometry.Scheme.Modules.Plus.unitPrecompose_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
abbrev originalNaturalUnitTotalPostcompose := @CategoryTheory.NatTrans.unitTotalPostcompose
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalNaturalUnitTotalPostcompose_app := CategoryTheory.NatTrans.unitTotalPostcompose_app
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalNaturalUnitTotalPostcompose_quasiIso :=
  AlgebraicGeometry.Scheme.Modules.Plus.unitTotalPostcompose_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalPlusIsoWeak := AlgebraicGeometry.Scheme.Modules.Plus.plus_iso_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalPlusNatTransPostcomposeWeak :=
  AlgebraicGeometry.Scheme.Modules.Plus.plus_nattrans_postcompose_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalPlusNatTransPrecomposeWeak :=
  AlgebraicGeometry.Scheme.Modules.Plus.plus_nattrans_precompose_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalPlusNatTransWeakComp :=
  AlgebraicGeometry.Scheme.Modules.Plus.plus_nattrans_comp_quasiIso
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
alias originalPlusWeakComp := AlgebraicGeometry.Scheme.Modules.Plus.plus_quasiIso_comp
end Quillen.SchemeSheaf

end
