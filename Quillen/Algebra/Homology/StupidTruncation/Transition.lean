/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Transition

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Waldhausen.GilletWaldhausen
export CochainComplex
  (stupidTruncGETransition stupidTruncGETransitionF stupidTruncGETransitionF_inclusion
  stupidTruncGETransitionNat stupidTruncGETransition_comp
  stupidTruncGETransition_degreewiseSplitMono stupidTruncGETransition_id
  stupidTruncGETransition_inclusion stupidTruncGETransition_naturality)
end Quillen.Waldhausen.GilletWaldhausen

end
