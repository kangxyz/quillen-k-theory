/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenCoefficientModel
public import Quillen.AlgebraicGeometry.Scheme.Affine.OpenPairBaseChange

/-!
# The original fixed-open relative coefficient diagram

Each algebra uses the specified pullback of the fixed original open. The unchanged exact
section reindexing forms a strict Model diagram and hence an actual strict prespectrum diagram.
The original fine-to-coarse maps give a literal natural transformation on that same diagram.
The identity-algebra object remains its actual pullback, rather than being identified with j.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The relative-open section Models on the fixed original pullbacks form a strict diagram. -/
def boundedFlatAffineSectionOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj a := boundedFlatAffineSectionOpenModel (inclusion j a)
  map {a b} f := boundedFlatAffineSectionOpenReindexModelMap
    (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)
  map_id a := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id boundedFlatAffineProjection a.right
  map_comp f g := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp boundedFlatAffineProjection f.right g.right

/-- The original iterated-S prespectrum functor applied to the genuine coarse section diagram. -/
def boundedFlatAffineSectionOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatAffineSectionOpenModelFunctor j ⋙ prespectrumFunctor

/-- Each coefficient arrow is exactly the original relative-open reindexing map. -/
theorem boundedFlatAffineSectionOpenPrespectrumFunctor_map {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSectionOpenPrespectrumFunctor j).map f =
      boundedFlatAffineSectionOpenReindexPrespectrumMap
        (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f) := rfl

/-- Changing the weak class on the same sections is strictly natural on the fixed-open diagram. -/
def boundedFlatAffineSectionOpenModelTransformation :
    Under.forget R ⋙ boundedFlatAffineSectionModelFunctor ⟶
      boundedFlatAffineSectionOpenModelFunctor j where
  app a := boundedFlatAffineSectionOpenModelMap (inclusion j a)
  naturality _ _ f := boundedFlatAffineSectionOpenModelMap_naturality
    (inclusion j _) (inclusion j _) f.right (openMap j f) (openMap_inclusion j f)

/-- Original realization retains the same fine-to-coarse natural transformation. -/
def boundedFlatAffineSectionOpenPrespectrumTransformation :
    Under.forget R ⋙ boundedFlatAffineSectionPrespectrumFunctor ⟶
      boundedFlatAffineSectionOpenPrespectrumFunctor j :=
  Functor.whiskerRight (boundedFlatAffineSectionOpenModelTransformation j) prespectrumFunctor

/-- Every component is the unchanged fine-to-relative-open section map. -/
theorem boundedFlatAffineSectionOpenPrespectrumTransformation_app (a : Under R) :
    (boundedFlatAffineSectionOpenPrespectrumTransformation j).app a =
      boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a) := rfl

end Quillen.PerfectComplexes
