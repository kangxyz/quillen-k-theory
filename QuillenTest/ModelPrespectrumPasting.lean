/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport

/-! Original Model pasting keeps both full tracks and the independent structure coordinate. -/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace QuillenTest.ModelPrespectrumPasting

open Quillen
variable {V W : Model.{u}} {F G G' H : V ⟶ W}
  (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
  (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
  (hη : ∀ A, W.waldhausen.weq (η.app A))
  (hθ : ∀ A, W.waldhausen.weq (θ.app A))
  (hη' : ∀ A, W.waldhausen.weq (η'.app A))
  (hθ' : ∀ A, W.waldhausen.weq (θ'.app A))
  (he : η ≫ θ = η' ≫ θ')

/-- The first face is the actual first two-track concatenation. -/
theorem first_route (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level n (0, (s, x)) =
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy θ hθ)).level n (s, x) :=
  ((prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level n).apply_zero _

/-- The other face is the actual second two-track concatenation. -/
theorem second_route (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level n (1, (s, x)) =
      ((prespectrumTransformationHomotopy η' hη').trans
        (prespectrumTransformationHomotopy θ' hθ')).level n (s, x) :=
  ((prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level n).apply_one _

/-- Comparison time, original homotopy time and structure time remain independent. -/
theorem three_times (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level (n + 1)
        (r, (s, (prespectrum V).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).level n (r, (s, x))) t :=
  (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he).comm n r s x t

/-- Source transport preserves the whole original degree-zero loop, including its loop time. -/
theorem transported_loop {F' : V ⟶ W} (h : F = F')
    (α : F'.functor ⟶ G.functor) (hα : ∀ A, W.waldhausen.weq (α.app A))
    (hα' : ∀ A, W.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor h) ≫ α).app A))
    (s q : unitInterval) (γ : (prespectrum V).space 0) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationHomotopy
        (eqToHom (congrArg Model.Hom.functor h) ≫ α) hα').level 0 (s, γ)) q =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from
        (prespectrumTransformationHomotopy α hα).level 0 (s, γ)) q := by
  rw [prespectrumTransformationHomotopy_source_transport_level h α hα hα']

end QuillenTest.ModelPrespectrumPasting
