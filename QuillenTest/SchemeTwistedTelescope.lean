/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeTwistedTelescope
public import QuillenTest.SchemeCurrentStageSquare

/-! # Actual global-section fixed-word telescope stability and scheme naturality -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass.SchemeNaturalSeed
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open QuillenTest.SchemeCurrentStageSquare
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u
namespace QuillenTest.SchemeTwistedTelescope

/-- The original global scalar action gives a stable comparison on every actual scheme. -/
example (X : Scheme.{u}ᵒᵖ) : IsStableEquivalence ((conjugacyTelescopeMap originalTrack).app X) :=
  model_conjugacyTelescopeMap_stable globalModel originalTrack X

/-- The same telescope maps are natural in arbitrary scheme morphisms. -/
example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (normalizedTelescope originalTrack).map f ≫ (conjugacyTelescopeMap originalTrack).app Y =
      (conjugacyTelescopeMap originalTrack).app X ≫ (twistedTelescope originalTrack).map f :=
  (conjugacyTelescopeMap originalTrack).naturality f

end QuillenTest.SchemeTwistedTelescope
