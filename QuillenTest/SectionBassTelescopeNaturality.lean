/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeNaturality

/-! Original coefficient-square consumers retain the actual signed boundary and cone cylinder. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassTelescopeNaturality

open Quillen
open PerfectComplexes
variable {A B : Arrow CommRingCat.{u}} (sq : A ⟶ B)

/-- Every original negative signed boundary commutes with the actual coefficient square. -/
theorem original_negative_boundary (q : ℕ)
    (z : stableHomotopyGroup
      (mappingCone (boundedFlatAffineSectionBassTelescopeMap A.hom)) (-(q : ℤ) - 1 + 1)) :
    boundedFlatAffineSectionBassTelescopeConeConnecting B.hom (-(q : ℤ) - 1)
        ((stableHomotopyFunctor (-(q : ℤ) - 1 + 1)).map
          (boundedFlatAffineSectionBassTelescopeConeMap sq) z) =
      (stableHomotopyFunctor (-(q : ℤ) - 1)).map
        (boundedFlatAffineSectionBassTelescopeMap sq.left)
          (boundedFlatAffineSectionBassTelescopeConeConnecting A.hom (-(q : ℤ) - 1) z) := by
  have h := boundedFlatAffineSectionBassTelescopeConeConnecting_naturality sq (-(q : ℤ) - 1)
  exact ConcreteCategory.congr_hom h z

/-- The actual cone map retains every original source point and the entire cone time. -/
theorem original_cone_cylinder (k : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionBassTelescope A.left).space k) :
    (boundedFlatAffineSectionBassTelescopeConeMap sq).map k
        (ReducedMappingCone.cylinder ((boundedFlatAffineSectionBassTelescope A.left).point k)
          ((boundedFlatAffineSectionBassTelescope A.right).point k)
          ((boundedFlatAffineSectionBassTelescopeMap A.hom).map k) (t, x)) =
      ReducedMappingCone.cylinder ((boundedFlatAffineSectionBassTelescope B.left).point k)
        ((boundedFlatAffineSectionBassTelescope B.right).point k)
        ((boundedFlatAffineSectionBassTelescopeMap B.hom).map k)
        (t, (boundedFlatAffineSectionBassTelescopeMap sq.left).map k x) := rfl

end QuillenTest.SectionBassTelescopeNaturality
