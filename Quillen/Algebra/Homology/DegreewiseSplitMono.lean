/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.CochainComplex.DegreewiseSplitMono

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Waldhausen
export CochainComplex
  (degreewiseSplitMono degreewiseSplitMono_mono degreewiseSplitMono_multiplicative
  degreewiseSplitMono_of_isIso degreewiseSplitMono_of_isZero degreewiseSplitMono_pushout)
end Quillen.Waldhausen

namespace Quillen.Waldhausen
/-- Historical name for the canonical Aglib declaration. -/
alias isSplitMono_of_isPushout := CategoryTheory.Limits.IsPushout.isSplitMono_inr
end Quillen.Waldhausen

end
