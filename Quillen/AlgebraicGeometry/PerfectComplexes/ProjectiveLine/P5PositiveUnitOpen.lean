/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
export AlgebraicGeometry.Scheme.Modules.Godement
  (local_total_unit_component openPullPlusIso openPushPlusIso openTotalBridge openTotalBridge_f
  openTotalBridge_quasiIso open_component_first_square open_component_second_square
  open_geometric_unit)
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev globalSpanLeg := @AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeGlobalLeg
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias globalSpanLeg_quasiIso :=
  AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeGlobalLeg_quasiIso
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev localPositive := @AlgebraicGeometry.Scheme.Modules.Godement.localPullbackPushforwardPlus
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev localSpanLeg := @AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeLocalLeg
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias localSpanLeg_quasiIso :=
  AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeLocalLeg_quasiIso
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev openPositiveComparison :=
  @AlgebraicGeometry.Scheme.Modules.Godement.openPullbackPushforwardComparison
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev openSpanTarget := @AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeSpanTarget
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias open_positive_unit_span := AlgebraicGeometry.Scheme.Modules.Godement.open_unit_span
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias open_positive_unit_span_component :=
  AlgebraicGeometry.Scheme.Modules.Godement.open_unit_span_component
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias open_positive_unit_span_factorized :=
  AlgebraicGeometry.Scheme.Modules.Godement.open_unit_span_factorized
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias positivePlusUnit_restrict_quasiIso :=
  AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit_restrict_quasiIso
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias pushPlus_quasiIso_flasque :=
  AlgebraicGeometry.Scheme.Modules.Plus.pushforward_quasiIso_of_flasque
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias quasiIso_of_QPlus_map_isIso := AlgebraicGeometry.Scheme.Modules.Plus.quasiIso_of_isIso_Q_map
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias quasiIso_of_plus_span := AlgebraicGeometry.Scheme.Modules.Plus.quasiIso_of_span
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev restrictedPositive :=
  @AlgebraicGeometry.Scheme.Modules.Godement.restrictedPullbackPushforwardPlus
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev restrictedPositiveUnit :=
  @AlgebraicGeometry.Scheme.Modules.Godement.restrictedPullbackPushforwardPlusUnit
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias restrictedPositiveUnit_factor :=
  AlgebraicGeometry.Scheme.Modules.Godement.restrictedPullbackPushforwardPlusUnit_factor
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
abbrev restrictedTotal := @AlgebraicGeometry.Scheme.Modules.Godement.restrictedTotalPlus
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias restrictedTotal_flasque :=
  AlgebraicGeometry.Scheme.Modules.Godement.restrictedTotalPlus_flasque
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
/-- Historical name for the canonical Aglib declaration. -/
alias totalTermsFlasque := AlgebraicGeometry.Scheme.Modules.Godement.totalPlus_terms_isFlasque
end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

end
