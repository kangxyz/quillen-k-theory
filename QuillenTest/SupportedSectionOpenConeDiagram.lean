/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenConeDiagram

/-!
# Consumers of the original coefficient-natural support cone

These tests retain arbitrary open-pair squares, original cylinder heights, original null-track
values and all cone points. Signed class lifting and the actual boundary use the unchanged
relative-open component, without any Bass-transition or full-open endpoint assertion.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.SupportedSectionOpenConeDiagram

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- An arbitrary original open-pair square preserves the whole null path at identical time. -/
theorem originalPairNullTrack {S : CommRingCat.{u}} {V : Scheme.{u}}
    (j' : V ⟶ Spec S) [IsOpenImmersion j'] (f : R ⟶ S) (l : V ⟶ U)
    (h : l ≫ j = j' ≫ Spec.map f) (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSectionOpenReindexPrespectrumMap j j' f l h).map n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j').level n
        (s, (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).map n x) :=
  boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient j j' f l h n s x

/-- Original coefficient maps on the cone diagram keep every cylinder height unchanged. -/
theorem originalCylinderMap {a b : Under R} (f : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionOpenConeFunctor j).map f).map n
        ((mappingConeHomotopy
          (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a))).level n
            (s, x)) =
      (mappingConeHomotopy
        (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j b))).level n
          (s, ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x) := rfl

/-- The original natural descent sends its actual cone cylinder to the specified null track. -/
theorem originalDescentCylinder (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionOpenConeTransformation j).app a).map n
        ((mappingConeHomotopy
          (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a))).level n
            (s, x)) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level n (s, x) := rfl

/-- Naturality holds on every original quotient-cone point, not just the two endpoint faces. -/
theorem originalConePointNaturality {a b : Under R} (f : a ⟶ b) (n : ℕ)
    (x : ((boundedFlatAffineSupportedSectionOpenConeFunctor j).obj a).space n) :
    ((boundedFlatAffineSupportedSectionOpenConeTransformation j).app b).map n
        (((boundedFlatAffineSupportedSectionOpenConeFunctor j).map f).map n x) =
      ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f).map n
        (((boundedFlatAffineSupportedSectionOpenConeTransformation j).app a).map n x) :=
  congrArg (fun q => q.map n x)
    ((boundedFlatAffineSupportedSectionOpenConeTransformation j).naturality f)

/-- Every negative relative-open coefficient class lifts through the original cone component. -/
theorem originalNegativeClassLift (a : Under R) (n : ℕ)
    (y : stableHomotopyGroup ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a)
      (-(n : ℤ) - 1)) :
    ∃ x, (stableHomotopyFunctor (-(n : ℤ) - 1)).map
      ((boundedFlatAffineSupportedSectionOpenConeTransformation j).app a) x = y := by
  let := boundedFlatAffineSupportedSectionOpenConeTransformation_isStableEquivalence j a
    (-(n : ℤ) - 1)
  exact (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor (-(n : ℤ) - 1)).map
    ((boundedFlatAffineSupportedSectionOpenConeTransformation j).app a))).surjective y

/-- The original coefficient component carries the entire original signed cone/fiber boundary. -/
theorem originalSignedBoundary (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (show mappingCone
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)) ⟶
            prespectrum (boundedFlatAffineSectionOpenModel (inclusion j a)) from
          (boundedFlatAffineSupportedSectionOpenConeTransformation j).app a) ≫
      stableFiberConnecting (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)) d =
      stableMappingConeConnecting
          (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a))
          (prespectrum_mappingConeFiberComparison_isStableEquivalence
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a))) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a))
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a))
            (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))) :=
  boundedFlatAffineSupportedSectionOpenConeMap_connecting (inclusion j a) d

end QuillenTest.SupportedSectionOpenConeDiagram
