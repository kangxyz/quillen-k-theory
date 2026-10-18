/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeCurrentStageTelescope
public import QuillenTest.SchemeCurrentStageSquare

/-! # Actual global-section telescope stability and scheme naturality -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open QuillenTest.SchemeCurrentStageSquare
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u
namespace QuillenTest.SchemeCurrentStageTelescope

/-- The original global scalar action gives a stable comparison on every actual scheme. -/
example (X : Scheme.{u}ᵒᵖ) : IsStableEquivalence ((telescopeMap originalTrack).app X) :=
  model_telescopeMap_stable globalModel originalTrack X

/-- The same telescope maps are natural in arbitrary scheme morphisms. -/
example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (currentTelescope originalTrack).map f ≫ (telescopeMap originalTrack).app Y =
      (telescopeMap originalTrack).app X ≫ (normalizedTelescope originalTrack).map f :=
  (telescopeMap originalTrack).naturality f

end QuillenTest.SchemeCurrentStageTelescope
