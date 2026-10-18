/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeTwistedNull
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
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original full-open arrow is the literal weak-change followed by restriction. -/
def fullMap := Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor ≫
  Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor

/-- The original selected null postcomposed by actual full-open restriction. -/
def fullNull : DiagramNullHomotopy
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f) where
  homotopy X := (((ParameterModels.supportedOpenNull f).homotopy X).postcomp
    (prespectrumMap ((ParameterModels.openRestriction f).app X))).cast
      (Category.assoc _ _ _)
      (by
        apply Hom.ext
        funext n
        ext x
        exact (prespectrumMap ((ParameterModels.openRestriction f).app X)).map_point n)
  naturality {X Y} g n r x := by
    exact (congrArg (fun k => k.map n
      (((ParameterModels.supportedOpenNull f).homotopy X).level n (r, x)))
      ((Functor.whiskerRight (ParameterModels.openRestriction f)
        prespectrumFunctor).naturality g)).symm.trans
      (congrArg (fun y => (prespectrumMap
        ((ParameterModels.openRestriction f).app Y)).map n y)
        ((ParameterModels.supportedOpenNull f).naturality g n r x))

/-- Every original full-open null slice commutes with the original scalar action. -/
theorem timeSlice_equivariant (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫ fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (fullNull f).homotopy (fullNull f).naturality r) := by
  intro X t
  apply Hom.ext
  funext n
  ext x
  exact (ParameterLaurentNull.fullOpenNull_laurentInterchange f X n r t x).symm

/-- The original two actual maps preserve the full-open scalar action. -/
theorem fullMap_equivariant : Equivariant (ambientTrack Q) (ambientTrack P) (fullMap f) :=
  (changeWeak_equivariant f).comp (openRestriction_equivariant f)

/-- The original full-open null on the current telescope. -/
def currentNull := currentInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The original full-open null on the normalized telescope. -/
def normalizedNull := normalizedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The original full-open null on the twisted telescope. -/
def twistedNull := twistedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The actual full-open original null is preserved at all points and all times. -/
theorem current_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (supportedTrack f)).obj X).space n) :
    ((telescopeMap (ambientTrack P)).app X).map n
      (((currentNull f).homotopy X).level n (r, x)) =
      ((normalizedNull f).homotopy X).level n
        (r, ((telescopeMap (supportedTrack f)).app X).map n x) :=
  telescopeMap_null _ _ _ _ _ (forget_equivariant f) (fullMap_equivariant f)
    (fullNull f) (timeSlice_equivariant f) X n r x

/-- The actual full-open original null is preserved at all points and all times. -/
theorem twisted_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (supportedTrack f)).obj X).space n) :
    ((conjugacyTelescopeMap (ambientTrack P)).app X).map n
      (((normalizedNull f).homotopy X).level n (r, x)) =
      ((twistedNull f).homotopy X).level n
        (r, ((conjugacyTelescopeMap (supportedTrack f)).app X).map n x) :=
  conjugacyTelescopeMap_null _ _ _ _ _ (forget_equivariant f) (fullMap_equivariant f)
    (fullNull f) (timeSlice_equivariant f) X n r x

end Quillen.PerfectComplexes.ParameterFullCurrentNull
