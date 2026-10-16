/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationPath

/-! # Forward original K-zero path evaluation with the supplied representative retained -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.SelfTrackKOperationPath
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Quillen.Waldhausen.Structure C) (V : Quillen.Waldhausen.Structure D)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The actual supplied path gives the forward normalization of the original level-one track. -/
theorem original_kzero_forward_path (H : Homotopy f f) (a : W.K 0)
    (γ : Path ((originalPrespectrum W).point 1) ((originalPrespectrum W).point 1))
    (hγ : W.smallModelKEquiv 0 a = ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧) :
    V.smallModelKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      loopKOneNormalization (basedLoopMap (f.map 1) (f.map_point 1) γ)
        ⟦H.pathSelfTrack 1 γ⟧ :=
  originalKSelfTrackOperation_path W V H a γ hγ

end QuillenTest.SelfTrackKOperationPath
