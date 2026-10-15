/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.AffineInduction

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeFiniteCoverInduction
export AlgebraicGeometry.Scheme.AffineInduction
  (of_compactOpen of_compactOpen_of_separated of_finiteAffineUnion_of_separated of_qcqs)
end Quillen.PerfectComplexes.ProjectiveLine.NativeFiniteCoverInduction

end
