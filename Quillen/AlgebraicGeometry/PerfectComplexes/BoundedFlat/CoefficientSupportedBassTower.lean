/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassTower

/-!
# Original native supported inclusion and localization at every Bass stage

The actual supported and ambient stages are literal strict Bass iterates of their
native Model diagrams. The original supported inclusion and identity change of
weakness are iterated unchanged. Every whole null-transition equation follows
from the proved time-slice seed square for the same initial null. Actual finite
Model growth propagates initial cone stability and supplies signed excision.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Literal finite Bass iterates of the actual native supported coefficient row. -/
def boundedFlatCoefficientSupportedBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedPrespectrumFunctor f)

/-- Literal finite Bass iterates of the original native fine ambient row. -/
def boundedFlatCoefficientAmbientBassDiagram (Q : Over (Spec R)) (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientAmbientPrespectrumFunctor Q)

/-- The unchanged finite supported transition is the original iterated supported seed. -/
def boundedFlatCoefficientSupportedBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedBassDiagram f i ⟶
      boundedFlatCoefficientSupportedBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedBassSeed f) i

/-- The unchanged finite ambient transition is the original iterated ambient seed. -/
def boundedFlatCoefficientAmbientBassTransition (Q : Over (Spec R)) (i : ℕ) :
    boundedFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedFlatCoefficientAmbientBassDiagram Q (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (boundedFlatCoefficientAmbientBassSeed Q) i

/-- The original supported inclusion at every unchanged finite Bass stage. -/
def boundedFlatCoefficientSupportedBassForget (i : ℕ) :
    boundedFlatCoefficientSupportedBassDiagram f i ⟶ boundedFlatCoefficientAmbientBassDiagram Q i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)

/-- The original ambient change to coarse relative-open weakness at every finite stage. -/
def boundedFlatCoefficientAmbientBassOpen (i : ℕ) :
    boundedFlatCoefficientAmbientBassDiagram Q i ⟶ boundedFlatCoefficientOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)

/-- The actual original supported inclusion commutes with every unchanged seed transition. -/
theorem boundedFlatCoefficientSupportedBassForget_transition (i : ℕ) :
    boundedFlatCoefficientSupportedBassForget f i ≫
        boundedFlatCoefficientAmbientBassTransition Q i =
      boundedFlatCoefficientSupportedBassTransition f i ≫
        boundedFlatCoefficientSupportedBassForget f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedBassSeed f) (boundedFlatCoefficientAmbientBassSeed Q)
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedFlatCoefficientSupportedBassSeed_forget f) i).symm

/-- The same original fine-to-coarse map commutes with every actual finite transition. -/
theorem boundedFlatCoefficientAmbientBassOpen_transition (i : ℕ) :
    boundedFlatCoefficientAmbientBassOpen f i ≫ boundedFlatCoefficientOpenBassTransition f i =
      boundedFlatCoefficientAmbientBassTransition Q i ≫
        boundedFlatCoefficientAmbientBassOpen f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientAmbientBassSeed Q) (boundedFlatCoefficientOpenBassSeed f)
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedFlatCoefficientAmbientBassSeed_open f) i).symm

/-- Iterate precisely the same original coefficient-natural whole supported localization null. -/
def boundedFlatCoefficientSupportedBassOpenNull (i : ℕ) :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedBassForget f i)
      (boundedFlatCoefficientAmbientBassOpen f i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenDiagramNull f) i

/-- All original null times preserve every unchanged finite supported/open transition. -/
theorem boundedFlatCoefficientSupportedBassOpenNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedFlatCoefficientOpenBassTransition f i).app a).map m
        (((boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) =
      ((boundedFlatCoefficientSupportedBassOpenNull f (i + 1)).homotopy a).level m
        (s, ((boundedFlatCoefficientSupportedBassTransition f i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenDiagramNull f)
    (boundedFlatCoefficientSupportedBassSeed f) (boundedFlatCoefficientOpenBassSeed f)
    (fun s ↦ boundedFlatCoefficientSupportedOpenNullTimeSlice_seed f s) i a m s x).symm

/-- Actual finite cone descent along the unchanged complete iterated supported localization null. -/
def boundedFlatCoefficientSupportedBassOpenConeMap (i : ℕ) :
    mappingConeDiagram (boundedFlatCoefficientSupportedBassForget f i) ⟶
      boundedFlatCoefficientOpenBassDiagram f i :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedBassForget f i)
    (boundedFlatCoefficientAmbientBassOpen f i)
    (boundedFlatCoefficientSupportedBassOpenNull f i).homotopy
    (boundedFlatCoefficientSupportedBassOpenNull f i).naturality

/-- Every original ambient inclusion face is exactly the original finite fine-to-coarse map. -/
theorem boundedFlatCoefficientSupportedBassOpenConeMap_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedBassForget f i).app a) ≫
        (boundedFlatCoefficientSupportedBassOpenConeMap f i).app a =
      (boundedFlatCoefficientAmbientBassOpen f i).app a := mappingConeInclusion_desc _ _ _

/-- Actual finite Model excision propagates stability of the original initial support cone. -/
theorem boundedFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedBassOpenConeMap f i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedModelFunctor f) (boundedFlatCoefficientSectionModelRow Q)
    (boundedFlatCoefficientOpenModelFunctor f)
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedFlatCoefficientSupportedOpenDiagramNull f)
    (fun a ↦ boundedFlatCoefficientSupportedOpenConeComparison_isStableEquivalence f a) i a

/-- Genuine finite Model growth supplies signed excision for the original supported inclusion. -/
theorem boundedFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientSupportedBassForget f i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedModelFunctor f) (boundedFlatCoefficientSectionModelRow Q)
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f) i a

end Quillen.PerfectComplexes
