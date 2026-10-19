/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowPresentationInput

/-! The original current input map and independent presentation map agree on every full value. -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace QuillenTest.SchemeModelRowPresentationInput
open NaturalTrack GeometricSeedCospan SchemeModelRowSeed
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))
  (M' : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)) ≅ 𝟭 (M'.obj (laurent.op.obj X)))
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).functor (unit' X) (unit' Y))
  (η : M ⟶ M')
  (hη : ∀ X, Preserves (η.app (laurent.op.obj X)).functor (unit X) (unit' X))


/-- Input naturality retains the actual comparison at every spectrum level and original value. -/
theorem comparison_level (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : ((SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M unit hunit)).obj X).space n) :
    (comparison M' unit' hunit' X).map n
        (((SchemeNaturalSeed.currentInputMap
          (ofModelUnits laurent.op coefficient M unit hunit)
          (ofModelUnits laurent.op coefficient M' unit' hunit')
          (Functor.whiskerRight η prespectrumFunctor)
          (inputEquivariance M unit hunit M' unit' hunit' η hη)).app X).map n x) =
      (inputMap M unit hunit M' unit' hunit' η hη X).map n
        ((comparison M unit hunit X).map n x) :=
  congrArg (fun a => a.map n x)
    (comparison_inputMap M unit hunit M' unit' hunit' η hη X)

end QuillenTest.SchemeModelRowPresentationInput
