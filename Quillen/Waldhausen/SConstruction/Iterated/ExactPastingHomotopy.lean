/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition

/-! Equal composites of actual weak transformations give relative comparisons between their
original normalized two-track pastings. The equality is supplied at the natural-transformation
level, before realization, rather than as a desired spectrum-level coherence. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G G' H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hG' : IsExact W.cof W.weq V.cof V.weq G')
  (hH : IsExact W.cof W.weq V.cof V.weq H)

/-- Actual equal transformation composites produce a whole endpoint-relative comparison of the
original normalized pastings, even when their intermediate exact functors differ. -/
def exactOriginalPrespectrumPastingHomotopy
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (hcomp : η ≫ θ = η' ≫ θ') :
    ((exactOriginalPrespectrumHomotopy W V hF hG η hη).trans
      (exactOriginalPrespectrumHomotopy W V hG hH θ hθ)).RelHomotopy
      ((exactOriginalPrespectrumHomotopy W V hF hG' η' hη').trans
        (exactOriginalPrespectrumHomotopy W V hG' hH θ' hθ')) := by
  have he : exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) =
    exactOriginalPrespectrumHomotopy W V hF hH (η' ≫ θ')
      (fun A ↦ V.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
    congr 1
  have J := exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ'
  rw [← he] at J
  exact (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).symm.trans J

end Quillen.Waldhausen.IteratedS
