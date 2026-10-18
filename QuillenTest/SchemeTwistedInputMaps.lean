/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Bass.SchemeTwistedInputMaps
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentTrack

/-! # The original supported and open maps commute with the actual telescope conjugacy -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example :
    normalizedInputMap (supportedTrack f) (ambientTrack Q)
        (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
        (forget_equivariant f) ≫ conjugacyTelescopeMap (ambientTrack Q) =
      conjugacyTelescopeMap (supportedTrack f) ≫
        twistedInputMap (supportedTrack f) (ambientTrack Q)
          (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
          (forget_equivariant f) :=
  conjugacyTelescopeMap_input_square _ _ _ (forget_equivariant f)

example :
    normalizedInputMap (ambientTrack Q) (openTrack f)
        (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
        (changeWeak_equivariant f) ≫ conjugacyTelescopeMap (openTrack f) =
      conjugacyTelescopeMap (ambientTrack Q) ≫
        twistedInputMap (ambientTrack Q) (openTrack f)
          (Functor.whiskerRight (ParameterModels.changeWeak f) prespectrumFunctor)
          (changeWeak_equivariant f) :=
  conjugacyTelescopeMap_input_square _ _ _ (changeWeak_equivariant f)

example :
    normalizedInputMap (openTrack f) (ambientTrack P)
        (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor)
        (openRestriction_equivariant f) ≫ conjugacyTelescopeMap (ambientTrack P) =
      conjugacyTelescopeMap (openTrack f) ≫
        twistedInputMap (openTrack f) (ambientTrack P)
          (Functor.whiskerRight (ParameterModels.openRestriction f) prespectrumFunctor)
          (openRestriction_equivariant f) :=
  conjugacyTelescopeMap_input_square _ _ _ (openRestriction_equivariant f)

#print axioms GeometricConeFixedWords.power_obj_naturality
#print axioms GeometricConeFixedWords.wordAt_naturality
#print axioms conjugatingIso_naturality
#print axioms twistedInput_transition
#print axioms conjugacyTelescopeMap_input_square
