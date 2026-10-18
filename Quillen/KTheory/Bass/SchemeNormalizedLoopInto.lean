/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeTwistedTransitions
public import Quillen.KTheory.Bass.FiniteLoopConjugacy

/-! # The literal normalized seed as the fixed casted finite-loop map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open FiniteLoopWordSlide
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Both constructions retain the identical complete functor association equality. -/
theorem normalizedTransition_loopInto (A : Track laurent.op coefficient F) (i : ℕ) :
    normalizedTransition A i = loopInto i (seed (coneTrack A i)) :=
  (loopInto_eq i
    (A := FiniteConeTopology.iterate squareFunctor i F)
    (B := FiniteConeTopology.iterate squareFunctor (i + 1) F)
    (seed (coneTrack A i))).symm

end Quillen.KTheory.Bass.SchemeNaturalSeed
