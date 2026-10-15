/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.Embedding.StupidTrunc.Layer

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Waldhausen.GilletWaldhausen
export CochainComplex
  (stupidTruncGELayerCokernelIso stupidTruncGELayerCokernelIso_projection
  stupidTruncGELayerFunctor stupidTruncGELayerProjection stupidTruncGELayerProjectionNat
  stupidTruncGELayerProjection_f stupidTruncGELayerProjection_naturality
  stupidTruncGELayerSequence stupidTruncGELayerSequenceSplitting
  stupidTruncGELayerSequence_degree_shortExact stupidTruncGELayerSequence_degreewiseSplitMono
  stupidTruncGELayerSequence_shortExact stupidTruncGELayer_zero)
end Quillen.Waldhausen.GilletWaldhausen

end
