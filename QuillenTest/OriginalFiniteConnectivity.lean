/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-!
# Concrete original-map inputs to finite homotopy excision

The actual strict section levels, arbitrary original geometric coefficient maps and all fiber
points satisfy the exact growing finite bounds. These consumers do not presume a cofiber gap
or infer connectivity from separation or chosen-point HEP.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.OriginalFiniteConnectivity

open Quillen

/-- Actual section levels have the sharper point-map bound in their original universe. -/
theorem actual_section_to_point (R : CommRingCat.{u}) (n : ℕ) :
    IsHomotopyConnectedMap (ContinuousMap.const
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).space (n + 1))
        (PUnit.unit : PUnit.{u + 2})) (n + 1) :=
  prespectrum_positiveLevel_toPoint_isHomotopyConnectedMap (boundedFlatAffineSectionModel R) n

/-- Every fiber point of an actual original coefficient map has the required finite vanishing. -/
theorem original_coefficient_all_fiber_points {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n k : ℕ) (hk : k < n)
    (y : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec S))).space (n + 1))
    (z : HomotopyFiber ((boundedFlatPerfectPrespectrumMap (Spec.map f)).map (n + 1)) y) :
    Subsingleton (HomotopyGroup.Pi k
      (HomotopyFiber ((boundedFlatPerfectPrespectrumMap (Spec.map f)).map (n + 1)) y) z) :=
  (originalPrespectrum_positiveLevel_isHomotopyConnectedMap
    (boundedFlatPerfectWaldhausen (Spec R)) (boundedFlatPerfectWaldhausen (Spec S))
    (boundedFlatPerfectPrespectrumMap (Spec.map f)) n).fiber_subsingleton y z k hk

/-- The lowest finite bound genuinely covers every target component, even at the first level. -/
theorem original_coefficient_first_level_coverage {R S : CommRingCat.{u}} (f : R ⟶ S)
    (y : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec S))).space 1) :
    ∃ x, Joined ((boundedFlatPerfectPrespectrumMap (Spec.map f)).map 1 x) y :=
  (originalPrespectrum_positiveLevel_isHomotopyConnectedMap
    (boundedFlatPerfectWaldhausen (Spec R)) (boundedFlatPerfectWaldhausen (Spec S))
    (boundedFlatPerfectPrespectrumMap (Spec.map f)) 0).component_surjective y

/-- Original coefficient maps act bijectively below the growing bound at every source point. -/
theorem original_coefficient_finite_bijection {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n k : ℕ) (hk : k < n)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space (n + 1)) :
    Function.Bijective (homotopyGroupMap (N := Fin k)
      ((boundedFlatPerfectPrespectrumMap (Spec.map f)).map (n + 1)) (x := x) rfl) :=
  (originalPrespectrum_positiveLevel_isHomotopyConnectedMap
    (boundedFlatPerfectWaldhausen (Spec R)) (boundedFlatPerfectWaldhausen (Spec S))
    (boundedFlatPerfectPrespectrumMap (Spec.map f)) n).homotopyGroupMap_bijective x k hk

/-- The bound on actual section homotopy groups includes arbitrary points and its top degree. -/
theorem actual_section_top_degree (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space (n + 1)) :
    Subsingleton (HomotopyGroup.Pi n
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).space (n + 1)) x) :=
  prespectrum_positiveLevel_homotopyGroup_subsingleton_at
    (boundedFlatAffineSectionModel R) n n (le_refl n) x

end QuillenTest.OriginalFiniteConnectivity
