/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeSeedRotationPointwise

/-!
# The actual finite Scheme seed rotation

The accepted whole geometric chi factorization, the original seed cospan, and the
fixed Bass-strength factorization imply the local base equation. The original inverse
loop transpose and the genuine two-cone geometric permutation remain explicit.
-/
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
open FiniteConeTopology IteratedLoopStrength FiniteLoopWords
open GeometricConeInterchange LoopFactor
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The genuine two-cone permutation gives the exact finite rotation of the original seed. -/
theorem seed_cone_rotation (A : Track laurent.op coefficient F) :
    (strictDiagramFunctor squareFunctor).map (seed A) ≫
        strengthDiagram squareFunctor (iterate squareFunctor 1 F) =
      Functor.whiskerRight (seed (coneTrack A 1)) parameterLoopingFunctor ≫
        (transposeIso (iterate squareFunctor 2 F)).inv ≫
        loopMap 2 (permutationNatIso F).hom := by
  apply NatTrans.ext
  funext X
  exact eq_of_heq (seed_cone_rotation_app_heq A X)

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
