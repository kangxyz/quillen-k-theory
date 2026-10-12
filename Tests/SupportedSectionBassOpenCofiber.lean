/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassOpenBoundary

/-!
# Unchanged supported finite Bass cone consumers

These clients retain the accepted support-forgetting map, honest relative-open endpoint,
original reversed initial null time, every cone-cylinder value, original coefficient arrow,
and signed boundary. In particular, the identity algebra retains its actual pullback open.
No geometric, topology or excision hypothesis is supplied beyond the original open immersion.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.Tests.SupportedSectionBassOpenCofiber
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Stage zero retains the actual original reversed null track on the actual identity pullback. -/
theorem originalInitialNull (m : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j 0).obj (Under.mk (𝟙 R))).space m) :
    ((boundedFlatAffineSupportedSectionBassOpenNull j 0).homotopy
      (Under.mk (𝟙 R))).level m (r, x) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy
        (inclusion j (Under.mk (𝟙 R)))).level m (r, x) := rfl

/-- The unchanged actual ambient map is the target face of the original finite cone comparison. -/
theorem originalTargetInclusion (n : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSupportedSectionBassForget j n).app a) ≫
        (boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a =
      (boundedFlatAffineSectionBassOpen j n).app a :=
  boundedFlatAffineSupportedSectionBassOpenConeMap_inclusion j n a

/-- The original cone cylinder keeps its entire recursively specified null time. -/
theorem originalConeCylinder (n : ℕ) (a : Under R) (m : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j n).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a).map m
      (ReducedMappingCone.cylinder
        (((boundedFlatAffineSupportedSectionBassDiagram j n).obj a).point m)
        (((boundedFlatAffineSectionBassDiagram n).obj a.right).point m)
        (((boundedFlatAffineSupportedSectionBassForget j n).app a).map m) (r, x)) =
      ((boundedFlatAffineSupportedSectionIterateOpenNull j n).homotopy a).level m (r, x) := rfl

/-- Every original coefficient arrow commutes on actual cone points before taking stable classes. -/
theorem originalCoefficient (n : ℕ) {a b : Under R} (f : a ⟶ b) (m : ℕ)
    (x : ((mappingConeDiagram (boundedFlatAffineSupportedSectionBassForget j n)).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app b).map m
        (((mappingConeDiagram (boundedFlatAffineSupportedSectionBassForget j n)).map f).map m x) =
      ((boundedFlatAffineSectionOpenBassDiagram j n).map f).map m
        (((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a).map m x) :=
  congrArg (fun g ↦ g.map m x)
    ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).naturality f)

/-- All negative stable groups use the same unchanged original finite support cone map. -/
theorem originalNegativeStableBijective (n k : ℕ) (a : Under R) :
    Function.Bijective ((stableHomotopyFunctor (-((k : ℤ) + 1))).map
      ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a)) := by
  let := boundedFlatAffineSupportedSectionBassOpenConeMap_isStableEquivalence j n a
    (-((k : ℤ) + 1))
  exact ConcreteCategory.bijective_of_isIso _

/-- The original signed boundary retains the actual supported inclusion and original fiber lift. -/
theorem originalSignedBoundary (n : ℕ) (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSupportedSectionBassForget j n).app a)) (d + 1)) :
    stableFiberConnecting ((boundedFlatAffineSectionBassOpen j n).app a) d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a) x) =
      (stableHomotopyFunctor d).map (homotopyFiberLift
        ((boundedFlatAffineSectionBassOpen j n).app a)
        ((boundedFlatAffineSupportedSectionBassForget j n).app a)
        ((boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a))
        (stableMappingConeConnecting ((boundedFlatAffineSupportedSectionBassForget j n).app a)
          (boundedFlatAffineSupportedSectionBassForget_coneFiber_isStableEquivalence j n a) d x) :=
  ConcreteCategory.congr_hom
    (boundedFlatAffineSupportedSectionBassOpenConeMap_connecting j n a d) x

end Quillen.Tests.SupportedSectionBassOpenCofiber
