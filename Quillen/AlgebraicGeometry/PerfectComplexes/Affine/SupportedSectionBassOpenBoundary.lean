/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassOpenCofiber

/-!
# The original signed support-to-relative-open boundary at every finite Bass stage

Actual finite Model growth is applied separately to the original supported Under-R source and
the unchanged ambient ring stage. Thus the same accepted support-forgetting map has genuine
cone-fiber excision. The actual relative-open descent carries its signed cone boundary to the
original relative-open fiber boundary, retaining the recursively specified whole null track.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Actual Model growth proves excision for the unchanged original support-forgetting map. -/
theorem boundedFlatAffineSupportedSectionBassForget_coneFiber_isStableEquivalence
    (n : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatAffineSupportedSectionBassForget j n).app a)) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ n
    (fun m ↦ modelDiagramIterate_point_homotopyExtensionProperty (laurentUnderSquareFunctor R)
      n (boundedFlatAffineSupportedSectionModelFunctor j) a (m + n + 2))
    (fun m ↦ modelDiagramIterate_point_homotopyExtensionProperty laurentSquareFunctor
      n boundedFlatAffineSectionModelFunctor a.right (m + n + 2))
    (fun m x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R)
      n (boundedFlatAffineSupportedSectionModelFunctor j) a m k hk x)
    (fun m x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_at laurentSquareFunctor
      n boundedFlatAffineSectionModelFunctor a.right m k hk x)

/-- The exact supported finite-stage cone descent retains the original signed boundary maps. -/
theorem boundedFlatAffineSupportedSectionBassOpenConeMap_connecting
    (n : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatAffineSupportedSectionBassOpenConeMap j n).app a) ≫
      stableFiberConnecting ((boundedFlatAffineSectionBassOpen j n).app a) d =
    stableMappingConeConnecting ((boundedFlatAffineSupportedSectionBassForget j n).app a)
      (boundedFlatAffineSupportedSectionBassForget_coneFiber_isStableEquivalence j n a) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedFlatAffineSectionBassOpen j n).app a)
          ((boundedFlatAffineSupportedSectionBassForget j n).app a)
          ((boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedFlatAffineSupportedSectionBassForget_coneFiber_isStableEquivalence j n a) d

end Quillen.PerfectComplexes
