/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Bass.SchemeInputTelescope
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack

/-! # Actual supported, ambient and open input squares at the original telescopes -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example :
    currentInputMap (supportedTrack f) (ambientTrack Q)
        (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
        (forget_equivariant f) ≫ telescopeMap (ambientTrack Q) =
      telescopeMap (supportedTrack f) ≫
        normalizedInputMap (supportedTrack f) (ambientTrack Q)
          (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
          (forget_equivariant f) :=
  telescopeMap_input_square _ _ _ (forget_equivariant f)

example :
    currentInputMap (ambientTrack Q) (openTrack f)
        (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
        (changeWeak_equivariant f) ≫ telescopeMap (openTrack f) =
      telescopeMap (ambientTrack Q) ≫
        normalizedInputMap (ambientTrack Q) (openTrack f)
          (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
          (changeWeak_equivariant f) :=
  telescopeMap_input_square _ _ _ (changeWeak_equivariant f)

example :
    currentInputMap (openTrack f) (ambientTrack P)
        (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor)
        (openRestriction_equivariant f) ≫ telescopeMap (ambientTrack P) =
      telescopeMap (openTrack f) ≫
        normalizedInputMap (openTrack f) (ambientTrack P)
          (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor)
          (openRestriction_equivariant f) :=
  telescopeMap_input_square _ _ _ (openRestriction_equivariant f)
