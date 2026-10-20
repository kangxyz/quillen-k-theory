/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.OriginalTriangleTransport
public import Quillen.Topology.Prespectrum.RelativeSurfaceValue

/-! The chosen transformation-equality transport preserves every original surface value. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
open CategoryTheory.Functor
open Quillen.LoopPrespectrum.Homotopy.RelHomotopy
namespace Quillen.Waldhausen.IteratedS
section
universe v
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

/-- Evaluate the original transport before expanding the small-model composition constructor. -/
theorem originalCompositionTransport_value (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (modelOf W)).space n) :
    surfaceValue (originalCompositionTransport W V hF hG hH h0F h0G h0H
      η θ τ hη hθ hτ he) n r s x =
      surfaceValue (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
        h0F h0G h0H η θ hη hθ) n r s x := by
  subst τ
  rfl

end
end Quillen.Waldhausen.IteratedS

