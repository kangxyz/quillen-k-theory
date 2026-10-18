/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquarePushoutNaturality
public import Quillen.Topology.Prespectrum.StrictSquarePushoutCells

/-!
# Regression for the original square-cone pushout isomorphism

Forward transport, an arbitrary strict span map, and inverse transport retain
the original total quotient map. The deepest original cell keeps its cone
height and two independent overlap parameters after that whole round trip.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.HomotopyPushout
open Quillen.LoopPrespectrum.StrictSquare
open Quillen.LoopPrespectrum.StrictSquare.Pushout
open scoped Topology unitInterval
universe u
namespace QuillenTest.StrictSquarePushout
variable {S₀ S₁ S₂ T₀ T₁ T₂ : Arrow (Arrow LoopPrespectrum.{u})}
    {f : S₀ ⟶ S₁} {g : S₀ ⟶ S₂} {f' : T₀ ⟶ T₁} {g' : T₀ ⟶ T₂}
    (h : SpanMorphism f g f' g')

/-- The same original inverse recovers the exact quotient map of the given span morphism. -/
theorem conjugation_recovers_map :
    (totalIso f g).hom ≫ mappingConeMap (strictSquareComparisonFunctor.map h.squareMap) ≫
        (totalIso f' g').inv =
      h.componentMap (strictSquareComparisonFunctor ⋙ mappingConeFunctor) := by
  rw [← Category.assoc, ← h.totalIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The original three independent cell parameters survive arbitrary natural transport. -/
theorem transported_three_parameters (n : ℕ) (r s t : unitInterval)
    (x : S₀.left.left.space n) :
    ((totalIso f g).hom ≫ mappingConeMap (strictSquareComparisonFunctor.map h.squareMap) ≫
      (totalIso f' g').inv).map n
        (cylinder (mappingConeMap (strictSquareComparisonFunctor.map f))
          (mappingConeMap (strictSquareComparisonFunctor.map g)) n
          (s, (mappingConeHomotopy (comparison S₀)).level n
            (r, cylinder S₀.left.hom S₀.hom.left n (t,x)))) =
      cylinder (mappingConeMap (strictSquareComparisonFunctor.map f'))
        (mappingConeMap (strictSquareComparisonFunctor.map g')) n
        (s, (mappingConeHomotopy (comparison T₀)).level n
          (r, cylinder T₀.left.hom T₀.hom.left n (t,h.source.left.left.map n x))) := by
  rw [conjugation_recovers_map]
  rfl

#print axioms Pushout.comm
#print axioms spanIso_comparison
#print axioms comparisonArrowIso
#print axioms totalIso
#print axioms SpanMorphism.totalIso_naturality
#print axioms SpanMorphism.totalIso_inv_naturality
#print axioms totalIso_three_parameters
#print axioms transported_three_parameters

end QuillenTest.StrictSquarePushout
