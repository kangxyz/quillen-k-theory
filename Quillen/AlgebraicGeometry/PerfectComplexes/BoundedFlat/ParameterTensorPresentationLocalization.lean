/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationActions
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentFullFiber
public import Quillen.KTheory.Bass.SchemeTrackSequentialNullTransport
public import Quillen.KTheory.Bass.SchemeTrackSequentialLiftTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorComparisonChoice

/-! The actual basic localization maps and original null
on normalized tensor ordinary presentations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterTensorPresentation
open GlobalSectionChangeIndex ParameterTensorNormalizedTrack
open SchemeTrackSequentialPresentation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original support forgetful map induces the actual ordinary-colimit map. -/
def basicForget : supportedDiagram f ⟶ ambientDiagram Q := ordinaryInputMap
  (ParameterModels.supported f) (ParameterModels.ambient Q)
  (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The original full-open restriction induces the actual ordinary-colimit map. -/
def basicRestriction : ambientDiagram Q ⟶ ambientDiagram P := ordinaryInputMap
  (ParameterModels.ambient Q) (ParameterModels.ambient P)
  (ambientTrack Q) (ambientTrack P) (ParameterFullCurrentNull.fullMap f) (fullMap_equivariant f)

/-- The actual ordinary presentation retains the original full-open null at every time. -/
def basicNull : DiagramNullHomotopy (basicForget f) (basicRestriction f) := ordinaryInputNull
  (ParameterModels.supported f) (ParameterModels.ambient Q)
  (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)
  (ParameterModels.ambient P) (ambientTrack P) (ParameterFullCurrentNull.fullMap f)
  (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f) (fullNull_equivariant f)

/-- The specified original null supplies the actual ordinary-presentation fiber lift. -/
def basicLift (X : Scheme.{u}ᵒᵖ) :
    supported f X ⟶ homotopyFiber ((basicRestriction f).app X) :=
  homotopyFiberLift ((basicRestriction f).app X) ((basicForget f).app X)
    ((basicNull f).homotopy X)

/-- The actual comparison preserves the original full-open null at exactly the same time. -/
theorem basicNull_comparison (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (q : ((SchemeNaturalSeed.currentTelescope
      (ParameterLaurentTrack.supportedTrack f)).obj X).space n) :
    type_of% (ordinaryInputNull_comparisonOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f) X n r q) :=
  ordinaryInputNull_comparisonOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f) X n r q
/-- The original basic localization theorem transports to this same-null ordinary lift. -/
theorem basicLift_integer_isStableEquivalence
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] :
    IsStableEquivalence (basicLift f (op integerBase)) := by
  have hs := ParameterFullCurrentNull.currentLift_integer_isStableEquivalence f
  dsimp only [ParameterFullCurrentNull.currentLift, ParameterFullCurrentNull.currentOpen,
    ParameterFullCurrentNull.currentForget, ParameterFullCurrentNull.currentNull] at hs
  have h := ordinaryInputLift_stableOfEq
    (ParameterModels.supported f) (ParameterModels.ambient Q) (ParameterModels.ambient P)
    (ParameterLaurentTrack.supportedTrack f) (supportedTrack f)
    (ParameterLaurentTrack.ambientTrack Q) (ambientTrack Q)
    (ParameterLaurentTrack.ambientTrack P) (ambientTrack P)
    (supportedTrack_transport_eq f) (ambientTrack_transport_eq Q) (ambientTrack_transport_eq P)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (ParameterLaurentTrack.forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (forget_equivariant f) (fullMap_equivariant f) (ParameterFullCurrentNull.fullNull f)
    (ParameterFullCurrentNull.timeSlice_equivariant f) (fullNull_equivariant f) (op integerBase) hs
  dsimp only [basicLift, basicNull, basicForget, basicRestriction,
    ambient, supported, ambientDiagram, supportedDiagram]
  exact h

/-- The fiber projection is exactly the actual ordinary support-forgetting map. -/
theorem basicLift_projection (X : Scheme.{u}ᵒᵖ) :
    basicLift f X ≫ homotopyFiberProjection ((basicRestriction f).app X) =
      (basicForget f).app X :=
  homotopyFiberLift_projection _ _ _

end Quillen.PerfectComplexes.ParameterTensorPresentation
