/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.PosetLoop

/-! # Exact original poset-resolution loops and their fixed basepoints -/

noncomputable section

open CategoryTheory Quillen Quillen.RankedChainOrder
open scoped Topology unitInterval

universe u

example (C : Type u) [SmallCategory C] (c : C) :
    (resolutionFunctor C).obj (resolutionVertex C c) = c := rfl

example (C : Type u) [SmallCategory C] (c : C) :
    resolutionLoopHomotopyEquiv C c
        (Path.refl (classifyingSpacePoint (resolutionVertex C c))) =
      Path.refl (classifyingSpacePoint c) :=
  resolutionLoopHomotopyEquiv_refl C c

-- The constructed inverse homotopies fix the original constant loop at every time.
example (C : Type u) [SmallCategory C] (c : C) (t : I) :
    (resolutionBasedHomotopyEquiv C c).loopRightHomotopy
        (t, Path.refl (classifyingSpacePoint c)) =
      Path.refl (classifyingSpacePoint c) :=
  (resolutionBasedHomotopyEquiv C c).loopRightHomotopy_refl t

example (C : Type u) [SmallCategory C] (c : C) (t : I) :
    (resolutionBasedHomotopyEquiv C c).loopLeftHomotopy
        (t, Path.refl (classifyingSpacePoint (resolutionVertex C c))) =
      Path.refl (classifyingSpacePoint (resolutionVertex C c)) :=
  (resolutionBasedHomotopyEquiv C c).loopLeftHomotopy_refl t
