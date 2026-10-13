/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy

/-! Original composite/concatenated faces and all three independent prespectrum coordinates. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u

namespace QuillenTest.PrespectrumCompositionHomotopy

open Quillen

variable {V W : Model.{u}} {F G H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))

lemma original_composite_face :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).at 0 =
      prespectrumTransformationHomotopy (η ≫ θ)
        (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).at_zero

lemma original_concatenation_face :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).at 1 =
      (prespectrumTransformationHomotopy η hη).trans (prespectrumTransformationHomotopy θ hθ) :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).at_one

lemma original_level_zero_loop (s t q : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level 0 (s, (t, γ))) q =
      stageTransformationCompositionHomotopy η θ hη hθ 0 (s, (t, γ q)) := rfl

lemma original_independent_structure (n : ℕ) (s t q : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level (n + 1)
        (s, (t, (prespectrum V).structureMap n x q)) =
      (prespectrum W).structureMap n
        ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (s, (t, x))) q :=
  (prespectrumTransformationCompositionHomotopy η θ hη hθ).comm n s t x q

lemma original_basepoint_line (n : ℕ) (s t : unitInterval) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n
        (s, (t, (prespectrum V).point n)) = (prespectrum W).point n :=
  ((prespectrumTransformationCompositionHomotopy η θ hη hθ).level n).eq_fst s
    (Or.inr (Or.inr rfl)) |>.trans
      ((prespectrumTransformationHomotopy (η ≫ θ)
        (fun A ↦ W.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))).at_point n t)

end QuillenTest.PrespectrumCompositionHomotopy
