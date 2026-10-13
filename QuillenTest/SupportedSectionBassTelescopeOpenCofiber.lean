/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeOpenCofiber

/-!
# Original supported telescope cone consumers

The initial original null track, both original cylinder times, actual Under coefficient maps,
negative signed groups and the unchanged single-boundary map are retained. The target remains
the original coarse relative-open telescope, without a classical negative-group identification.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.Scheme.AffineOpenPair
universe u
namespace QuillenTest.SupportedSectionBassTelescopeOpenCofiber

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The stage-zero cylinder retains the initial original null track on the actual pulled-back open.
-/
theorem originalInitialNullCylinder (a : Under R) (m : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j 0).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a).map m
      (ReducedMappingCone.cylinder
        (((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).point m)
        ((boundedFlatAffineSectionBassTelescope a.right).point m)
        (((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map m)
        (r, Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) m 0 (t, x))) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n ↦ (boundedFlatAffineSectionOpenBassTransition j n).app a) m 0
          (t, (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a)).level m
            (r, x)) := rfl

/-- Every original ambient finite stage retains its exact target face in the telescope cone. -/
theorem originalTargetStage (i : ℕ) (a : Under R) :
    (boundedFlatAffineSectionBassTelescopeInclusion i).app a.right ≫
      mappingConeInclusion ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a) ≫
        (boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a =
      (boundedFlatAffineSectionBassOpen j i).app a ≫
        (boundedFlatAffineSectionOpenBassTelescopeInclusion j i).app a := by
  exact (congrArg (fun f ↦ (boundedFlatAffineSectionBassTelescopeInclusion i).app a.right ≫ f)
    (boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_inclusion j a)).trans
      (congrArg (fun f ↦ f.app a) (boundedFlatAffineSectionBassTelescopeInclusion_open j i))

/-- The unchanged Under coefficient arrows commute before passage to stable homotopy classes. -/
theorem originalCoefficient {a b : Under R} (f : a ⟶ b) (m : ℕ)
    (x : ((mappingConeDiagram (boundedFlatAffineSupportedSectionBassTelescopeForget j)).obj a).space
      m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app b).map m
        (((mappingConeDiagram (boundedFlatAffineSupportedSectionBassTelescopeForget j)).map f).map
          m x) =
      ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).map f).map m
        (((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a).map m x) :=
  congrArg (fun g ↦ g.map m x)
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).naturality f)

/-- The actual supported telescope cone comparison gives every negative signed bijection. -/
theorem originalNegativeBijective (a : Under R) (q : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((q : ℤ) + 1))).map
      ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a)) := by
  let := boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_isStableEquivalence j a
    (-((q : ℤ) + 1))
  exact ConcreteCategory.bijective_of_isIso _

/-- The boundary uses the same original telescope null track in its actual fiber lift. -/
theorem originalSignedBoundary (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)) (d + 1)) :
    stableFiberConnecting ((boundedFlatAffineSectionBassTelescopeOpen j).app a) d
      ((stableHomotopyFunctor (d + 1)).map
        ((boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap j).app a) x) =
      (stableHomotopyFunctor d).map (homotopyFiberLift
        ((boundedFlatAffineSectionBassTelescopeOpen j).app a)
        ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
        ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a))
        (stableMappingConeConnecting
          ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a)
          (boundedFlatAffineSupportedSectionBassTelescopeForget_coneFiber_isStableEquivalence j a)
          d x) :=
  ConcreteCategory.congr_hom
    (boundedFlatAffineSupportedSectionBassTelescopeOpenConeMap_connecting j a d) x

end QuillenTest.SupportedSectionBassTelescopeOpenCofiber
