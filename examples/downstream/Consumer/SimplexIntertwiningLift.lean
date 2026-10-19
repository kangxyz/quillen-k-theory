/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexIntertwiningLift

/-! Entire original intertwining word and its independent parameters. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Consumer.SimplexIntertwiningLift
variable {V W T U : Model.{u}}
  (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
  (α : F.functor ≅ F.functor) (i : (F ≫ b).functor ≅ (a ≫ G).functor)
  (θ : G.functor ⟶ G.functor)
  (hα : ∀ X, W.waldhausen.weq (α.hom.app X))
  (hθ : ∀ X, U.waldhausen.weq (θ.app X))
  (hi : ∀ X, U.waldhausen.weq (i.hom.app X))
  (he : whiskerRight α.hom b.functor ≫ i.hom = i.hom ≫ whiskerLeft a.functor θ)

/-- Every level retains the exact original two-triangle intertwining comparison. -/
theorem whole (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (SimplexIntertwiningLift.simplex F G a b α i) n
      (SimplexIntertwiningLift.parameter (r, s), x) =
      (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he).level n
        (r, (s, x)) :=
  SimplexIntertwiningLift.native F G a b α i θ hα hθ hi he n r s x

/-- The client obtains a whole lift using only the original transformations and their equation. -/
theorem original_lift : HomotopyLift (SimplexIntertwiningLift.simplex F G a b α i)
    SimplexIntertwiningLift.parameter
    (prespectrumTransformationIntertwiningHomotopy F G a b α.hom θ i.hom hα hθ hi he) :=
  SimplexIntertwiningLift.native F G a b α i θ hα hθ hi he

end Consumer.SimplexIntertwiningLift
