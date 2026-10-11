/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision
public import Quillen.Topology.Prespectrum.ConeStableNaturality

/-!
# Unconditional original stable cone sequences for actual S-models

The genuine original cone-to-fiber theorem discharges the excision premise of the signed cone
sequence for every map between actual S-models. It likewise discharges both row premises for
stable comparison of their literal mapping cones under an unchanged strict arrow square.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS

/-- The actual original S-map boundary has all three recurring signed exactness positions. -/
theorem prespectrum_stableMappingConeLongExactSequence {W V : Model.{u}}
    (f : prespectrum W ⟶ prespectrum V) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (stableMappingConeConnecting f (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
        d) ∧
    Function.Exact
      (stableMappingConeConnecting f (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
        d) ((stableHomotopyFunctor d).map f) ∧
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  stableMappingConeLongExactSequence f
    (prespectrum_mappingConeFiberComparison_isStableEquivalence f) d

/-- Stable original sides preserve the literal mapping cone of maps between actual S-models. -/
theorem prespectrum_mappingConeMap_isStableEquivalence {W V W' V' : Model.{u}}
    {f : prespectrum W ⟶ prespectrum V} {g : prespectrum W' ⟶ prespectrum V'}
    (sq : Arrow.mk f ⟶ Arrow.mk g)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision sq
    (prespectrum_mappingConeFiberComparison_isStableEquivalence f)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence g) hl hr

/-- The independently universed original model has an exact original target/cone pair. -/
theorem originalPrespectrum_stableMappingCone_exact_target
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V)
    (d : ℤ) : Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  stableMappingCone_exact_target f
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence W V f) d

end Quillen.Waldhausen.IteratedS
