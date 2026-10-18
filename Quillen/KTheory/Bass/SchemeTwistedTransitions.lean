/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeCurrentStageSquare
public import Quillen.KTheory.Bass.GeometricConeFixedWords

/-! # The fixed geometric and loop words on normalized Scheme stages -/
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
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteLoopWords FiniteConeTopology GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The fixed loop reversal followed by the exact accumulated geometric word, including casts. -/
def conjugatingIso (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    normalized squareFunctor i F ≅ normalized squareFunctor i F :=
  reversalIso i (iterate squareFunctor i F) ≪≫ (loopFunctor i).mapIso (wordAt i F)

/-- The normalized seed followed by the specified cyclic loop and geometric insertion words. -/
def twistedTransition (A : Track laurent.op coefficient F) (i : ℕ) :
    normalized squareFunctor i F ⟶ normalized squareFunctor (i + 1) F :=
  normalizedTransition A i ≫ (cyclicIso i (iterate squareFunctor (i + 1) F)).hom ≫
    loopMap (i + 1) (betaAt i F).hom

/-- The stage isomorphism has precisely the prescribed execution order. -/
theorem conjugatingIso_hom (i : ℕ) :
    (conjugatingIso i F).hom =
      (reversalIso i (iterate squareFunctor i F)).hom ≫ loopMap i (wordAt i F).hom := rfl

end Quillen.KTheory.Bass.SchemeNaturalSeed
