/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionOpenSeedNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassOpenCofiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassOpenTower
public import Quillen.KTheory.Bass.StrictDiagramIterateNullTimeSlice

/-!
# Original supported relative-open null tracks preserve every Bass transition

The genuine original Laurent/null square gives the full initial seed square. The unchanged
Bass time-slice law propagates it through every finite iterate. The existing ambient restriction
isomorphism changes no null value, so this is the same original finite support/open null family.
There is no supplied seed or eventual transition compatibility hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Every original coarse transition preserves the same full finite-stage null track. -/
theorem boundedFlatAffineSupportedSectionBassOpenNull_transition
    (n : ℕ) (a : Under R) (m : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j n).obj a).space m) :
    ((boundedFlatAffineSectionOpenBassTransition j n).app a).map m
        (((boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a).level m (r, x)) =
      ((boundedFlatAffineSupportedSectionBassOpenNull j (n + 1)).homotopy a).level m
        (r, ((boundedFlatAffineSupportedSectionBassTransition j n).app a).map m x) := by
  exact (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionOpenDiagramNull j)
    (boundedFlatAffineSupportedSectionBassSeed j) (boundedFlatAffineSectionOpenBassSeed j)
    (fun r => boundedFlatAffineSupportedSectionOpenNullTimeSlice_seed j r) n a m r x).symm

end Quillen.PerfectComplexes
