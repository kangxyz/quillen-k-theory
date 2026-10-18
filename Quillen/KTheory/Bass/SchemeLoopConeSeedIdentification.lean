/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeLoopConeTrackIdentification
public import Quillen.KTheory.Bass.SchemeBassFunctorIdentification

/-! # The unchanged looped cone seed in the geometric cospan -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The looped cone seed is the original geometric cospan seed, including its endpoint casts. -/
theorem seed_loopCone_heq_bassSeed (A : Track laurent.op coefficient F) :
    HEq (seed ((coneTrack A 1).loop))
      (WholeSeedCospan.seed
        (GeometricSquareInterchange.geometricSquare
          ((strictDiagramFunctor squareFunctor).obj F))
        (bassTrack F A.homotopy A.naturality)
        (bassTrack_naturality F A.homotopy A.naturality)) := by
  simp only [seed, sourceTrack_loopConeTrack A]
  dsimp only [bassFunctor_obj_eq, iterate]
  rfl

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
