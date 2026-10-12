/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.Monoidal.RightIterationFactorization
public import Mathlib.CategoryTheory.Groupoid

/-!
# The two actual finite-stage factorization tracks

These are the two routes in the twisted group-completion argument. They share
literal endpoints but are not asserted equal or homotopic relative endpoints.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]

/-- The original associator interchanges left and right translation. -/
def leftRightCommutationIso (P Q : C) : tensorLeft P ⋙ tensorRight Q ≅
    tensorRight Q ⋙ tensorLeft P :=
  NatIso.ofComponents (fun X ↦ asIso ((leftStep Q P).app X))
    (fun {_ _} f ↦ (leftStep Q P).naturality f)

/-- The original iterated associator intertwines left translation and stabilization. -/
def leftIterateCommutationIso (e P : C) (k : ℕ) :
    tensorLeft P ⋙ EndofunctorTelescope.iterate (tensorRight e) k ≅
      EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P :=
  NatIso.ofComponents
    (fun X ↦ asIso ((EndofunctorTelescope.commuteIterate (leftStep e P) k).app X))
    (fun {_ _} f ↦ (EndofunctorTelescope.commuteIterate (leftStep e P) k).naturality f)

/-- Apply the original factorization first and then the distinguished left translation. -/
def factorizationUpperTrack (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P) :
    EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P ≅
      tensorRight Q ⋙ tensorLeft P ⋙ tensorLeft P :=
  Functor.isoWhiskerRight G (tensorLeft P)

/-- First commute the distinguished translation past stabilization, apply the
factorization there, and use the original associator to align the endpoint. -/
def factorizationLowerTrack (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P) :
    EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P ≅
      tensorRight Q ⋙ tensorLeft P ⋙ tensorLeft P :=
  (leftIterateCommutationIso e P k).symm ≪≫
    Functor.isoWhiskerLeft (tensorLeft P) G ≪≫
      Functor.isoWhiskerRight (leftRightCommutationIso P Q) (tensorLeft P)

/-- At a finite stage the original braiding is genuinely a natural isomorphism. -/
def rightLeftBraidingIso [BraidedCategory C] (P : C) : tensorRight P ≅ tensorLeft P :=
  NatIso.ofComponents (fun X ↦ β_ X P)
    (fun {_ _} f ↦ BraidedCategory.braiding_naturality_left f P)

/-- The upper track uses exactly the left translate of the chosen factorization component. -/
theorem factorizationUpperTrack_hom_app (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P)
    (X : C) :
    (factorizationUpperTrack e P Q k G).hom.app X = (tensorLeft P).map (G.hom.app X) := rfl

/-- The lower track retains the inverse iterated associator and the final associator. -/
theorem factorizationLowerTrack_hom_app (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P)
    (X : C) :
    (factorizationLowerTrack e P Q k G).hom.app X =
      (leftIterateCommutationIso e P k).inv.app X ≫ G.hom.app ((tensorLeft P).obj X) ≫
        (tensorLeft P).map ((leftStep Q P).app X) := rfl

end Quillen.TranslationTelescope
