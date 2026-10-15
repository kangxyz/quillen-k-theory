/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Maps

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Waldhausen.GilletWaldhausen
export CochainComplex
  (stupidTruncGE stupidTruncGEFunctor stupidTruncGEInclusion stupidTruncGEInclusionF
  stupidTruncGEInclusionNat stupidTruncGEInclusion_degreewiseSplitMono
  stupidTruncGEInclusion_f_of_le stupidTruncGEInclusion_naturality stupidTruncGEXIso
  stupidTruncGE_isZero_X)
export HomologicalComplex
  (stupidTruncXIso_hom_d)
end Quillen.Waldhausen.GilletWaldhausen

end
