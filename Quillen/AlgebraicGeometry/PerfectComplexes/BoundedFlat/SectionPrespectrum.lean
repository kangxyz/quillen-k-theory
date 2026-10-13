/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionReindexExact
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-!
# A genuine strict prespectrum diagram of bounded-flat affine sections

The actual section categories have object and hom universe `u+1`, so they directly form iterated-S
models. Exact coefficient restrictions preserve the pointwise chosen zeros literally. The existing
prespectrum functor therefore supplies literal identity and composition laws on the original maps.

This is the actual section S-prespectrum. Comparison with the original geometric prespectrum uses
the unequal-hom-universe evaluation equivalence and remains separate from a strict Bass seed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual section category is already a small model at universe `u+1`. -/
def boundedFlatAffineSectionModel (R : CommRingCat.{u}) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatAffineSections R), boundedFlatAffineSectionWaldhausen R⟩

/-- Exact coefficient restriction preserves the original chosen model zero literally. -/
def boundedFlatAffineSectionModelMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionModel R ⟶ boundedFlatAffineSectionModel S where
  functor := boundedFlatAffineSectionsMap f
  exact := boundedFlatAffineSectionsMap_exact f
  zero := by
    change (boundedFlatAffineSectionsMap f).obj (boundedFlatAffineSectionWaldhausen R).zero =
      (boundedFlatAffineSectionWaldhausen S).zero
    rw [boundedFlatAffineSectionWaldhausen_zero, boundedFlatAffineSectionsMap_sectionZero,
      boundedFlatAffineSectionWaldhausen_zero]

/-- The actual section models form a strict functor on all coefficient maps. -/
def boundedFlatAffineSectionModelFunctor : CommRingCat.{u} ⥤ Model.{u+1} where
  obj := boundedFlatAffineSectionModel
  map := boundedFlatAffineSectionModelMap
  map_id R := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id boundedFlatAffineProjection R
  map_comp f g := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp boundedFlatAffineProjection f g

/-- The original iterated-S prespectrum functor applied to the actual strict section models. -/
def boundedFlatAffineSectionPrespectrumFunctor : CommRingCat.{u} ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatAffineSectionModelFunctor ⋙ prespectrumFunctor

/-- The zero-space homotopy sets retain the actual section Waldhausen K-groups. -/
def boundedFlatAffineSectionZeroSpaceEquiv (R : CommRingCat.{u}) (n : ℕ) :
    (boundedFlatAffineSectionWaldhausen R).K n ≃
      HomotopyGroup.Pi n ((boundedFlatAffineSectionPrespectrumFunctor.obj R).space 0)
        ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point 0) :=
  zeroSpaceHomotopyEquiv (boundedFlatAffineSectionModel R) n

/-- The induced zero-space map is the original K-map of the actual coefficient restriction. -/
theorem boundedFlatAffineSectionZeroSpaceEquiv_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) (n : ℕ) (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    boundedFlatAffineSectionZeroSpaceEquiv S n
        (KMap (boundedFlatAffineSectionsMap_exact f) n a) =
      homotopyGroupMap ((boundedFlatAffineSectionPrespectrumFunctor.map f).map 0)
        ((boundedFlatAffineSectionPrespectrumFunctor.map f).map_point 0)
        (boundedFlatAffineSectionZeroSpaceEquiv R n a) := by
  rw [KMap_eq_piMap_of_zeroEq (boundedFlatAffineSectionsMap_exact f)
    (boundedFlatAffineSectionModelMap f).zero]
  exact loopShiftEquiv_natural n (deloopingMap (boundedFlatAffineSectionsMap_exact f)).hom
    (stageMap_point 0 (boundedFlatAffineSectionModelMap f)) a

end Quillen.PerfectComplexes
