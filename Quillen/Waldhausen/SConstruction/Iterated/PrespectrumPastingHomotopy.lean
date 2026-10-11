/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition

/-!
# Pasting the original Model transformation tracks

An equality of actual Model transformation composites gives a relative comparison of their
original two-track concatenations. This form avoids applying `AsSmall` a second time and is used
for the common-universe section evaluation comparisons.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS

/-- Equal composites compare the original Model tracks, with no further normalization. -/
def prespectrumPastingHomotopy {V W : Model.{u}} {F G G' H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.waldhausen.weq (θ'.app A))
    (hcomp : η ≫ θ = η' ≫ θ') :
    ((prespectrumTransformationHomotopy η hη).trans
      (prespectrumTransformationHomotopy θ hθ)).RelHomotopy
      ((prespectrumTransformationHomotopy η' hη').trans
        (prespectrumTransformationHomotopy θ' hθ')) := by
  have he : prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) =
    prespectrumTransformationHomotopy (η' ≫ θ')
      (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
    congr 1
  have J := prespectrumTransformationCompositionHomotopy η' θ' hη' hθ'
  rw [← he] at J
  exact (prespectrumTransformationCompositionHomotopy η θ hη hθ).symm.trans J

end Quillen.Waldhausen.IteratedS
