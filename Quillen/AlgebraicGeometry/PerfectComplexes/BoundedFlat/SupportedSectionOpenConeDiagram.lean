/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNullCoefficient
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenConeComparison
public import Quillen.CategoryTheory.ArrowDiagrams

/-!
# The actual coefficient-natural supported-section cone descent

The existing arrow-diagram interchange forms the original pointwise cone diagram of the actual
support-forgetting natural transformation. The whole original coefficient-natural null tracks
give a literal natural transformation from that diagram to the original coarse relative-open
diagram. Each unchanged component is stably equivalent by the genuine geometric comparison.
No Bass cofiber-preservation or telescope transition compatibility is assumed here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Scheme.AffineOpenPair Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original support-forgetting diagram, followed by the actual mapping-cone functor. -/
def boundedFlatAffineSupportedSectionOpenConeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  (ArrowDiagrams.toDiagram.obj
    (Arrow.mk (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j))) ⋙
      mappingConeFunctor

/-- Every object is the cone of the literal original support-forgetting map. -/
theorem boundedFlatAffineSupportedSectionOpenConeFunctor_obj (a : Under R) :
    (boundedFlatAffineSupportedSectionOpenConeFunctor j).obj a =
      mappingCone (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)) := rfl

/-- The original whole null track makes the original cone descents strictly coefficient-natural. -/
def boundedFlatAffineSupportedSectionOpenConeTransformation :
    boundedFlatAffineSupportedSectionOpenConeFunctor j ⟶
      boundedFlatAffineSectionOpenPrespectrumFunctor j where
  app a := boundedFlatAffineSupportedSectionOpenConeMap (inclusion j a)
  naturality a b f := mappingConeDesc_naturality
    ((ArrowDiagrams.toDiagram.obj
      (Arrow.mk (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j))).map f)
    (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a))
    (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j b))
    ((boundedFlatAffineSectionOpenPrespectrumFunctor j).map f)
    (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j a))
    (boundedFlatAffineSupportedSectionOpenNullHomotopy (inclusion j b))
    ((boundedFlatAffineSectionOpenPrespectrumTransformation j).naturality f)
    (boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
      (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f))

/-- Each component remains the unchanged original supported-section cone descent. -/
theorem boundedFlatAffineSupportedSectionOpenConeTransformation_app (a : Under R) :
    (boundedFlatAffineSupportedSectionOpenConeTransformation j).app a =
      boundedFlatAffineSupportedSectionOpenConeMap (inclusion j a) := rfl

/-- Actual original geometric excision proves stability at every original coefficient algebra. -/
theorem boundedFlatAffineSupportedSectionOpenConeTransformation_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSupportedSectionOpenConeTransformation j).app a) :=
  boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence (inclusion j a)

end Quillen.PerfectComplexes
