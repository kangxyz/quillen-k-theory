/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationObject

/-! # Original object evaluation with the canonical zero rebase retained -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u v
namespace QuillenTest.SelfTrackKOperationObject
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)
  {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original object class evaluates to the forward component automorphism class. -/
theorem exact_object_forward (e : F ≅ F) (A : C) :
    originalKSelfTrackOperation W V (exactOriginalPrespectrumIsoHomotopy W V hF hF e) 0
      (W.kZeroObjectClass A) = V.automorphismKOneClass (e.app A) :=
  originalKSelfTrackOperation_object W V hF e A

/-- Both independent parameters survive in the full original weak-arrow square. -/
theorem exact_object_track_coordinates (h0 : F.obj W.zero = V.zero)
    (η : F ⟶ F) (hη : ∀ A, V.weq (η.app A)) (A : C) (s t : unitInterval) :
    (originalPrespectrumTransformationHomotopy W V hF hF h0 h0 η hη).pathSelfTrack 1
        (originalSmallModelObjectLoop W A) s t =
      V.smallModelDeloopingHomeomorph (V.weakObjectSquareLoopPath (η.app A) (hη A) s t) :=
  originalTransformation_object_track_apply W V hF h0 η hη A s t

end QuillenTest.SelfTrackKOperationObject
