/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSquareExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutStableEquivalence
public import Quillen.Topology.Prespectrum.StrictSquareStableEquivalence

/-!
# Actual Bass-endofunctor stable preservation on finite geometric section stages

Every original span and span-to-Laurent comparison satisfies the proved topology and finite
excision bounds. Hence a strict square map between actual finite stages gives a stable original
looped-cone map whenever its four original corner maps are stable. Applied to the literal Laurent
coefficient square, this proves objectwise stable preservation by the existing Bass endofunctor
on strict natural transformations. All point-set, growth and excision inputs are discharged.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual looped-cone square map is stable from its four unchanged stable corner maps. -/
theorem boundedFlatAffineSectionBass_squareMap_isStableEquivalence
    (i j : ℕ) (Q Q' : Arrow (Arrow CommRingCat.{u}))
    (a : (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj Q ⟶
      (boundedFlatAffineSectionBassDiagram j).mapArrow.mapArrow.obj Q')
    (h00 : IsStableEquivalence a.left.left) (h01 : IsStableEquivalence a.left.right)
    (h10 : IsStableEquivalence a.right.left) (h11 : IsStableEquivalence a.right.right) :
    IsStableEquivalence (strictSquareLoopedConeFunctor.map a) := by
  apply strictSquareLoopedConeFunctor_map_isStableEquivalence_of_excision a
    (boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence i Q)
    (boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence j Q')
    _ h11
  exact boundedFlatAffineSectionBass_pushoutMap_isStableEquivalence
    i i i j j j Q.left.left Q.left.right Q.right.left Q'.left.left Q'.left.right Q'.right.left
    _ _ _ _ a.left.left a.left.right a.right.left a.left.w.symm
    (congrArg (fun f ↦ f.left) a.w).symm h00 h01 h10

/-- The original Bass endofunctor preserves objectwise stable finite-stage transformations. -/
theorem boundedFlatAffineSectionBass_functorMap_isStableEquivalence
    (i j : ℕ) (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶
      boundedFlatAffineSectionBassDiagram j)
    (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) :
    IsStableEquivalence ((KTheory.Bass.strictRingDiagramFunctor.map η).app R) := by
  exact boundedFlatAffineSectionBass_squareMap_isStableEquivalence i j
    (PolynomialBaseChange.laurentSquareFunctor.obj R)
    (PolynomialBaseChange.laurentSquareFunctor.obj R)
    (((Functor.mapArrowFunctor (Arrow CommRingCat) (Arrow LoopPrespectrum)).map
      ((Functor.mapArrowFunctor CommRingCat LoopPrespectrum).map η)).app
        (PolynomialBaseChange.laurentSquareFunctor.obj R))
    (hη _) (hη _) (hη _) (hη _)

end Quillen.PerfectComplexes
