/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactSelfTrackStableOperation

/-! # Original exact-functor inverse tracks on negative stable groups -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.ExactSelfTrackStableOperation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D) {F : C ⥤ D}
variable (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The inverse of the actual natural isomorphism negates the negative-one operation. -/
theorem negative_one_inverse (e : F ≅ F) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF e.symm).stableOperation (-1) =
      -(exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation (-1) :=
  exactIsoSelfTrack_stableOperation_symm W V hF e (-1)

/-- No replacement by a literal constant identity track is assumed. -/
theorem zero_identity :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (Iso.refl F)).stableOperation 0 = 0 :=
  exactIsoSelfTrack_stableOperation_refl W V hF 0

end QuillenTest.ExactSelfTrackStableOperation
