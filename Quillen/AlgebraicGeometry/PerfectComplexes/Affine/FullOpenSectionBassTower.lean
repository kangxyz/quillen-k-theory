/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeed
public import Quillen.KTheory.Bass.ModelDiagramConnectivity

/-!
# The actual fine full-open Bass tower

Every finite stage is the strict Bass iterate of the original full-open section Model
prespectrum, and every transition is the iterate of its constructed forward Laurent seed.
The Model-stage topology supplies separation and the original chosen-point extension property.
These constructions require only the specified open immersion.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The finite fine stage is the literal Bass iterate of the original section diagram. -/
def boundedFlatAffineFullOpenSectionBassDiagram (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatAffineFullOpenSectionPrespectrumFunctor j)

/-- The initial fine stage is exactly the original full-open section diagram. -/
theorem boundedFlatAffineFullOpenSectionBassDiagram_zero :
    boundedFlatAffineFullOpenSectionBassDiagram j 0 =
      boundedFlatAffineFullOpenSectionPrespectrumFunctor j := rfl

/-- Every transition is the same iterated image of the original forward Laurent seed. -/
def boundedFlatAffineFullOpenSectionBassTransition (i : ℕ) :
    boundedFlatAffineFullOpenSectionBassDiagram j i ⟶
      boundedFlatAffineFullOpenSectionBassDiagram j (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenSectionBassSeed j) i

/-- The original fine seed is the unchanged first transition. -/
theorem boundedFlatAffineFullOpenSectionBassTransition_zero :
    boundedFlatAffineFullOpenSectionBassTransition j 0 =
      boundedFlatAffineFullOpenSectionBassSeed j := rfl

/-- Every actual finite fine Model stage has its original T1 level topology. -/
instance boundedFlatAffineFullOpenSectionBassDiagram_spaceT1Space
    (i : ℕ) (a : Under R) (n : ℕ) :
    T1Space (((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space n) :=
  modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
    (boundedFlatAffineFullOpenSectionModelFunctor j) a n

/-- The original chosen point retains its genuine extension property at every finite stage. -/
theorem boundedFlatAffineFullOpenSectionBassDiagram_point_homotopyExtensionProperty
    (i : ℕ) (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).point n))) :=
  modelDiagramIterate_point_homotopyExtensionProperty (laurentUnderSquareFunctor R) i
    (boundedFlatAffineFullOpenSectionModelFunctor j) a n

end Quillen.PerfectComplexes
