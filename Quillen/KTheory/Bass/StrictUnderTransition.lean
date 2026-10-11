/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictUnderDiagram
public import Quillen.KTheory.Bass.StrictDiagramMap
public import Quillen.CategoryTheory.Functor.CommutingTransition

/-!
# Original Bass transitions under restriction and seed maps

A proved original seed square remains commutative under every finite Bass iterate.
Restriction along Under.forget identifies the actual iterated transition with the
same original ring transition, through its specified literal functor equality.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.KTheory.Bass

/-- The canonical original stage identification is the specified functor equality component. -/
def strictRingDiagramRestrictionIterateMap (R : CommRingCat.{u}) (n : ℕ)
    (F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :
    (strictDiagramIterate (PolynomialBaseChange.laurentUnderSquareFunctor R) n).obj
        ((strictRingDiagramRestriction R).obj F) ⟶
      (strictRingDiagramRestriction R).obj ((strictRingDiagramIterate n).obj F) :=
  eqToHom (Functor.congr_obj (strictRingDiagramRestriction_comp_iterate R n) F)

/-- The specified restriction equality keeps every original finite transition. -/
theorem strictRingDiagramRestrictionIterateMap_transition (R : CommRingCat.{u}) (n : ℕ)
    {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}} (η : F ⟶ strictRingDiagramFunctor.obj F) :
    strictDiagramTransition (PolynomialBaseChange.laurentUnderSquareFunctor R)
        (strictRingDiagramUnderSeed R η) n ≫
        strictRingDiagramRestrictionIterateMap R (n + 1) F =
      strictRingDiagramRestrictionIterateMap R n F ≫
        (strictRingDiagramRestriction R).map ((strictRingDiagramIterate n).map η) :=
  Quillen.Functor.commuting_transition (strictRingDiagramRestriction R)
    strictRingDiagramFunctor (strictRingDiagramIterate n)
    (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R))
    (strictDiagramIterate (PolynomialBaseChange.laurentUnderSquareFunctor R) n)
    (strictRingDiagramRestriction_comp_bass R)
    (strictRingDiagramRestriction_comp_iterate R n)
    (strictRingDiagramRestriction_comp_iterate R (n + 1)) η

/-- An actual seed-preserving map enters each unchanged ambient ring stage after restriction. -/
def strictRingDiagramRestrictionIterateArrow (R : CommRingCat.{u}) (n : ℕ)
    {F : Under R ⥤ LoopPrespectrum.{w}} {G : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (a : F ⟶ (strictRingDiagramRestriction R).obj G) :
    (strictDiagramIterate (PolynomialBaseChange.laurentUnderSquareFunctor R) n).obj F ⟶
      (strictRingDiagramRestriction R).obj ((strictRingDiagramIterate n).obj G) :=
  (strictDiagramIterate (PolynomialBaseChange.laurentUnderSquareFunctor R) n).map a ≫
    strictRingDiagramRestrictionIterateMap R n G

/-- The original seed square and specified restriction transports preserve every transition. -/
theorem strictRingDiagramRestrictionIterateArrow_transition (R : CommRingCat.{u}) (n : ℕ)
    {F : Under R ⥤ LoopPrespectrum.{w}} {G : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (σ : F ⟶ (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).obj F)
    (η : G ⟶ strictRingDiagramFunctor.obj G)
    (a : F ⟶ (strictRingDiagramRestriction R).obj G)
    (h : σ ≫ (strictDiagramFunctor (PolynomialBaseChange.laurentUnderSquareFunctor R)).map a =
      a ≫ strictRingDiagramUnderSeed R η) :
    strictRingDiagramRestrictionIterateArrow R n a ≫
        (strictRingDiagramRestriction R).map ((strictRingDiagramIterate n).map η) =
      strictDiagramTransition (PolynomialBaseChange.laurentUnderSquareFunctor R) σ n ≫
        strictRingDiagramRestrictionIterateArrow R (n + 1) a := by
  exact (CommSq.horiz_comp
    ⟨(strictDiagramTransition_map
      (PolynomialBaseChange.laurentUnderSquareFunctor R) σ _ a h n).symm⟩
    ⟨(strictRingDiagramRestrictionIterateMap_transition R n η).symm⟩).w

end Quillen.KTheory.Bass
