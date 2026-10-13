/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Relative skeleta from the empty subcomplex

The relative skeleton of the bottom-subcomplex inclusion is exactly the
ordinary skeleton. This equality preserves the chosen stages and inclusions.
-/
@[expose] public section

universe u

namespace Quillen

/-- The relative skeleton of the empty inclusion is the ordinary skeleton. -/
theorem skeletonOfMono_bot (X : SSet.{u}) (n : ℕ) :
    SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι) n = X.skeleton n := by
  simp [SSet.skeletonOfMono, SSet.Subcomplex.range]

end Quillen
