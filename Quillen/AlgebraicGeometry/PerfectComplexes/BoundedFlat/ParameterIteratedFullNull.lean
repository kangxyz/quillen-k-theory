/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeIteratedInputNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull

/-! # The actual original seed-iterate full-open diagram and its selected null -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original iterated-seed supported inclusion. -/
def iteratedForget := iteratedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The original iterated-seed full-open restriction. -/
def iteratedOpen := iteratedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The same selected full-open null on the original seed-iterate telescope. -/
def iteratedNull := iteratedInputNull (supportedTrack f) (ambientTrack Q) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f)
  (forget_equivariant f) (fullMap_equivariant f) (fullNull f) (timeSlice_equivariant f)

/-- The original same-null full-open lift on the original seed-iterate model. -/
def iteratedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((iteratedOpen f).app X) ((iteratedForget f).app X)
    ((iteratedNull f).homotopy X)

end Quillen.PerfectComplexes.ParameterFullCurrentNull
