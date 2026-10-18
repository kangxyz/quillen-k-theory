/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeTwistedAdjacent

/-! # The actual initial fixed-word square needs no later permutation equivariance -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass Quillen.LoopPrespectrum
open NaturalTrack SchemeNaturalSeed GeometricSeedCospan
open GeometricConeFixedWords
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace QuillenTest.SchemeTwistedAdjacent

/-- At the initial stage the actual accumulated word is identity. -/
example {F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}} (A : Track laurent.op coefficient F) :
    normalizedTransition A 0 ≫ (conjugatingIso 1 F).hom =
      (conjugatingIso 0 F).hom ≫ twistedTransition A 0 := by
  apply twisted_adjacent_of_seed_square
  have h : (wordAt 0 F).hom =
      𝟙 (FiniteConeTopology.iterate squareFunctor 0 F) := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

end QuillenTest.SchemeTwistedAdjacent
