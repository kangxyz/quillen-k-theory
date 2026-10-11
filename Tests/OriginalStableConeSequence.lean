/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ConeStableSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-!
# Original signed stable cone exactness and naturality consumers

These statements keep the actual section and normalized geometric coefficient arrows,
original mapping cones, signed degree shifts and exact original square maps. They exercise
kernel lifting, the transported boundary, its naturality and genuine stable cone invariance.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.OriginalStableConeSequence

/-- The actual section coefficient boundary uses the original signed fiber comparison. -/
def actualSectionBoundary {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ) :
    stableHomotopyGroup (mappingCone (boundedFlatAffineSectionPrespectrumFunctor.map f)) (d + 1) ⟶
      stableHomotopyGroup (boundedFlatAffineSectionPrespectrumFunctor.obj R) d :=
  stableMappingConeConnecting (boundedFlatAffineSectionPrespectrumFunctor.map f)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _) d

/-- Original boundary values lie in the actual coefficient kernel in every signed degree. -/
theorem actual_section_boundary_kernel {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionPrespectrumFunctor.map f))
      (d + 1)) :
    (stableHomotopyFunctor d).map (boundedFlatAffineSectionPrespectrumFunctor.map f)
      (actualSectionBoundary f d x) = 0 :=
  (stableMappingConeConnecting_exact_source (boundedFlatAffineSectionPrespectrumFunctor.map f)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _) d _).mpr ⟨x, rfl⟩

/-- Any original coefficient kernel class is the actual boundary of an original cone class. -/
theorem actual_section_boundary_surjects_kernel {R S : CommRingCat.{u}}
    (f : R ⟶ S) (d : ℤ)
    (x : stableHomotopyGroup (boundedFlatAffineSectionPrespectrumFunctor.obj R) d)
    (hx : (stableHomotopyFunctor d).map (boundedFlatAffineSectionPrespectrumFunctor.map f) x = 0) :
    ∃ y, actualSectionBoundary f d y = x :=
  (stableMappingConeConnecting_exact_source (boundedFlatAffineSectionPrespectrumFunctor.map f)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _) d x).mp hx

/-- Kernel classes for the unchanged original geometric cone inclusion lift in negative degrees. -/
theorem original_negative_kernel_lift {R S : CommRingCat.{u}} (f : R ⟶ S) (k : ℕ)
    (x : stableHomotopyGroup (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec S)))
      (-(Int.ofNat k + 1)))
    (hx : (stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (Spec.map f))) x = 0) :
    ∃ y, (stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (boundedFlatPerfectPrespectrumMap (Spec.map f)) y = x :=
  (originalPrespectrum_stableMappingCone_exact_target
    (boundedFlatPerfectWaldhausen (Spec R)) (boundedFlatPerfectWaldhausen (Spec S))
    (boundedFlatPerfectPrespectrumMap (Spec.map f)) _ x).mp hx

/-- The literal cone map of an original stable section square is invertible in negative degrees. -/
theorem actual_section_square_negative_iso {R S R' S' : CommRingCat.{u}}
    {f : R ⟶ S} {g : R' ⟶ S'}
    (sq : Arrow.mk (boundedFlatAffineSectionPrespectrumFunctor.map f) ⟶
      Arrow.mk (boundedFlatAffineSectionPrespectrumFunctor.map g))
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map (mappingConeMap sq)) :=
  prespectrum_mappingConeMap_isStableEquivalence sq hl hr _

/-- The entire original square induces the expected boundary equality with its signed shift. -/
theorem actual_section_boundary_naturality {R S R' S' : CommRingCat.{u}}
    {f : R ⟶ S} {g : R' ⟶ S'}
    (sq : Arrow.mk (boundedFlatAffineSectionPrespectrumFunctor.map f) ⟶
      Arrow.mk (boundedFlatAffineSectionPrespectrumFunctor.map g)) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionPrespectrumFunctor.map f))
      (d + 1)) :
    actualSectionBoundary g d ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq) x) =
      (stableHomotopyFunctor d).map sq.left (actualSectionBoundary f d x) :=
  ConcreteCategory.congr_hom (stableMappingConeConnecting_naturality sq
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _) d) x

end Quillen.Tests.OriginalStableConeSequence
