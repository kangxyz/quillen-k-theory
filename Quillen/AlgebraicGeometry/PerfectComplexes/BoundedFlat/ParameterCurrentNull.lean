/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeInputNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentNull

/-! # The original supported parameter null on current and normalized towers -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed NaturalTrack
universe u
namespace Quillen.PerfectComplexes.ParameterCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- Every original null time slice intertwines the original Laurent actions. -/
theorem timeSlice_equivariant (r : unitInterval) :
    Equivariant (supportedTrack f) (openTrack f)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫
          Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.openModel f ⋙ prespectrumFunctor))
        (ParameterModels.supportedOpenNull f).homotopy
        (ParameterModels.supportedOpenNull f).naturality r) := by
  intro X t
  apply Hom.ext
  funext n
  ext x
  exact (ParameterLaurentNull.supportedOpenNull_laurentInterchange f X n r t x).symm

/-- The actual current telescope null uses precisely the selected zero-to-open null. -/
def currentNull := currentInputNull (supportedTrack f) (ambientTrack Q) (openTrack f)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
  (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
  (forget_equivariant f) (changeWeak_equivariant f)
  (ParameterModels.supportedOpenNull f) (timeSlice_equivariant f)

/-- The actual normalized telescope null uses the same selected null at each finite stage. -/
def normalizedNull := normalizedInputNull (supportedTrack f) (ambientTrack Q) (openTrack f)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
  (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
  (forget_equivariant f) (changeWeak_equivariant f)
  (ParameterModels.supportedOpenNull f) (timeSlice_equivariant f)

/-- The actual telescope comparison preserves every time of the original supported null. -/
theorem null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (supportedTrack f)).obj X).space n) :
    ((telescopeMap (openTrack f)).app X).map n
      (((currentNull f).homotopy X).level n (r, x)) =
      ((normalizedNull f).homotopy X).level n
        (r, ((telescopeMap (supportedTrack f)).app X).map n x) :=
  telescopeMap_null _ _ _ _ _ (forget_equivariant f) (changeWeak_equivariant f)
    (ParameterModels.supportedOpenNull f) (timeSlice_equivariant f) X n r x

end Quillen.PerfectComplexes.ParameterCurrentNull
