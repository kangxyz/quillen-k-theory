/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorNormalizedSupport

/-! Whole parameter tracks from the actual normalized tensor units on the original Models. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterTensorNormalizedTrack
open GlobalSectionChangeIndex GlobalTensorNormalizedSupport GeometricSeedCospan NaturalTrack

private theorem units_track_congr (M : Scheme.{u}ᵒᵖ ⥤ Model.{u + 1})
    (α β : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
    (hα : ∀ {X Y} (g : X ⟶ Y),
      Preserves (M.map (laurent.op.map g)).functor (α X) (α Y))
    (hβ : ∀ {X Y} (g : X ⟶ Y),
      Preserves (M.map (laurent.op.map g)).functor (β X) (β Y)) (h : α = β) :
    ofModelUnits laurent.op coefficient M α hα =
      ofModelUnits laurent.op coefficient M β hβ := by
  subst β
  rfl

/-- Actual parameter pullback preserves the normalized genuine ambient tensor unit. -/
theorem ambientUnit_naturality (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves ((ParameterModels.ambient Q).map (laurent.op.map g)).functor
      (ambientUnit Q X) (ambientUnit Q Y) := by
  rw [ambientUnit_eq, ambientUnit_eq]
  exact ParameterLaurentUnit.ambientUnit_naturality Q g

/-- The normalized genuine tensor unit induces the actual ambient parameter track. -/
def ambientTrack (Q : Scheme.{u}) :
    Track laurent.op coefficient (ParameterModels.ambient Q ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.ambient Q)
    (ambientUnit Q) (ambientUnit_naturality Q)

/-- The entire ambient track is the original parameter track. -/
theorem ambientTrack_eq (Q : Scheme.{u}) :
    ambientTrack Q = ParameterLaurentTrack.ambientTrack Q := by
  have h : ambientUnit Q = ParameterLaurentUnit.ambientUnit Q := funext (ambientUnit_eq Q)
  unfold ambientTrack ParameterLaurentTrack.ambientTrack
  congr

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual supported lift of normalized tensor multiplication induces this track. -/
def supportedTrack :
    Track laurent.op coefficient (ParameterModels.supported f ⋙ prespectrumFunctor) :=
  ofModelUnits laurent.op coefficient (ParameterModels.supported f)
    (supportedUnit f) (supportedUnit_naturality f)

/-- The entire supported track retains the original support predicate and every time. -/
theorem supportedTrack_eq : supportedTrack f = ParameterLaurentTrack.supportedTrack f := by
  have h : supportedUnit f = ParameterLaurentTrack.supportedUnit f :=
    funext (supportedUnit_eq f)
  exact units_track_congr (ParameterModels.supported f) _ _
    (supportedUnit_naturality f) (ParameterLaurentTrack.supportedUnit_naturality f) h

end Quillen.PerfectComplexes.ParameterTensorNormalizedTrack
