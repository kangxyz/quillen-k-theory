/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCompositionHomotopy

/-! Original normalized composite and concatenation faces, and their actual conjugated
components. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v
namespace Quillen.Tests.ExactCompositionHomotopy

section Exact
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hH : IsExact W.cof W.weq V.cof V.weq H)
  (η : F ⟶ G) (θ : G ⟶ H)
  (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))

lemma original_normalized_composite :
    (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).at 0 =
      exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
        (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) :=
  (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).at_zero

lemma original_normalized_concatenation :
    (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).at 1 =
      (exactOriginalPrespectrumHomotopy W V hF hG η hη).trans
        (exactOriginalPrespectrumHomotopy W V hG hH θ hθ) :=
  (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ).at_one

lemma normalized_composite_component (A : C) :
    (normalizedWeakTransformation hF hH (η ≫ θ)).app A =
      (normalizedWeakTransformation hF hG η).app A ≫
        (normalizedWeakTransformation hG hH θ).app A :=
  congrArg (fun α ↦ α.app A) (normalizedWeakTransformation_comp W V hF hG hH η θ)

end Exact


end Quillen.Tests.ExactCompositionHomotopy
