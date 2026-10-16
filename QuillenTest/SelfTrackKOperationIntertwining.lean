/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationIntertwining

/-! # The actual original K-zero map retains its full intertwining data -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.SelfTrackKOperationIntertwining
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f g : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Equality of original K-zero homomorphisms uses the given track and full relative square. -/
theorem original_kzero_transport
    (H : Homotopy f f) (K : Homotopy g g) (T : Homotopy f g)
    (J : (H.trans T).RelHomotopy (T.trans K)) :
    originalKSelfTrackOperation W V H 0 = originalKSelfTrackOperation W V K 0 :=
  originalKSelfTrackOperation_intertwine W V H K T J 0

end QuillenTest.SelfTrackKOperationIntertwining
