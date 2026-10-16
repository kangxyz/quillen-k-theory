/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableConcatenation

/-! # Original negative stable operations retain literal time composition -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableConcatenation
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- No eventual stability assumption is needed for negative-degree time composition. -/
theorem negative_one_concatenation (H K : Homotopy f f) :
    (H.trans K).stableOperation (-1) = K.stableOperation (-1) + H.stableOperation (-1) :=
  H.stableOperation_trans K (-1)

/-- The literal constant track is zero even in negative degree. -/
theorem negative_one_constant : (Homotopy.refl f).stableOperation (-1) = 0 :=
  Homotopy.stableOperation_refl (-1)

end QuillenTest.SelfTrackStableConcatenation
