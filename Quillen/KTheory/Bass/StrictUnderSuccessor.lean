/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictDiagramSuccessorMap
public import Quillen.KTheory.Bass.StrictUnderTransition

/-!
# Restriction coherence of the original strict Bass successor maps

The specified restriction equalities commute with the actual right-successor maps, including
all equality-induced endpoint transports. Naturality extends this coherence to arbitrary arrows
into a restricted ring diagram, without requiring any seed compatibility hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u w
namespace Quillen.KTheory.Bass

/-- The exact finite restriction transports commute with the original right-successor map. -/
theorem strictRingDiagramRestrictionIterateMap_successor (R : CommRingCat.{u}) (i : ℕ)
    (G : CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :
    strictDiagramSuccessorMap (PolynomialBaseChange.laurentUnderSquareFunctor R)
        ((strictRingDiagramRestriction R).obj G) i ≫
        (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
          (strictRingDiagramRestrictionIterateMap R i G) =
      strictRingDiagramRestrictionIterateMap R (i + 1) G ≫
        Functor.whiskerLeft (Under.forget R)
          (strictDiagramSuccessorMap PolynomialBaseChange.laurentSquareFunctor G i) := by
  change strictDiagramSuccessorMap (PolynomialBaseChange.laurentUnderSquareFunctor R)
        ((strictRingDiagramRestriction R).obj G) i ≫
        (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
          (strictRingDiagramRestrictionIterateMap R i G) =
      strictRingDiagramRestrictionIterateMap R (i + 1) G ≫
        (strictRingDiagramRestriction R).map
          (strictDiagramSuccessorMap PolynomialBaseChange.laurentSquareFunctor G i)
  simp only [strictDiagramSuccessorMap, strictRingDiagramRestrictionIterateMap,
    eqToHom_map, eqToHom_trans]

/-- Every original arrow into a restricted ring diagram retains the same successor square. -/
theorem strictRingDiagramRestrictionIterateArrow_successor (R : CommRingCat.{u}) (i : ℕ)
    {F : Under R ⥤ LoopPrespectrum.{w}} {G : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (a : F ⟶ (strictRingDiagramRestriction R).obj G) :
    strictDiagramSuccessorMap (PolynomialBaseChange.laurentUnderSquareFunctor R) F i ≫
        (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map
          (strictRingDiagramRestrictionIterateArrow R i a) =
      strictRingDiagramRestrictionIterateArrow R (i + 1) a ≫
        Functor.whiskerLeft (Under.forget R)
          (strictDiagramSuccessorMap PolynomialBaseChange.laurentSquareFunctor G i) := by
  simp only [strictRingDiagramRestrictionIterateArrow, Functor.map_comp]
  rw [← Category.assoc, ← strictDiagramSuccessorMap_naturality,
    Category.assoc, strictRingDiagramRestrictionIterateMap_successor, Category.assoc]

end Quillen.KTheory.Bass
