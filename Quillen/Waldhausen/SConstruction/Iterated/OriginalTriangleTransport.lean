/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy

/-! Field preservation for the exact original transformation-equality transport. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hH : IsExact W.cof W.weq V.cof V.weq H)
  (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
  (h0H : H.obj W.zero = V.zero)
  (η : F ⟶ G) (θ : G ⟶ H) (τ : F ⟶ H)
  (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
  (hτ : ∀ A, V.weq (τ.app A)) (he : η ≫ θ = τ)

/-- The same source-equality transport used by the native binary comparison, before realization. -/
def originalCompositionTransport :
    (originalPrespectrumTransformationHomotopy W V hF hH h0F h0H τ hτ).RelHomotopy
      ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).trans
        (originalPrespectrumTransformationHomotopy W V hG hH h0G h0H θ hθ)) := by
  have J := originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
    h0F h0G h0H η θ hη hθ
  simpa only [he] using J

/-- Rewriting the composite transformation preserves every point of the old whole triangle. -/
theorem originalCompositionTransport_level (n : ℕ) :
    ((originalCompositionTransport W V hF hG hH h0F h0G h0H η θ τ hη hθ hτ he).level
      n).toContinuousMap =
      ((originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
        h0F h0G h0H η θ hη hθ).level n).toContinuousMap := by
  subst τ
  rfl

end Quillen.Waldhausen.IteratedS
