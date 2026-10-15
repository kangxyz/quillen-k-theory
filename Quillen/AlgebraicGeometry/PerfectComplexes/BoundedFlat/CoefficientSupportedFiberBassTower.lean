/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassTower

/-!
# Original intersection-support inclusion and localization at every Bass stage

Finite fiber and auxiliary ambient stages are literal strict Bass iterates of
their actual native Model diagrams. The original inclusion, identity weakness
change and complete supported null are iterated unchanged. Every null-time
transition equation follows from the actual original time-slice seed square.
Native initial cone stability and genuine finite Model excision pass to each
same original finite cone, without any stabilization or localization premise.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Literal finite Bass iterates of the actual native supported coefficient row. -/
def boundedFlatCoefficientSupportedFiberBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T)

/-- Literal finite Bass iterates of the original native fine ambient row. -/
def boundedFlatCoefficientSupportedAmbientBassDiagram (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedAmbientPrespectrumFunctor T)

/-- The unchanged finite supported transition is the original iterated supported seed. -/
def boundedFlatCoefficientSupportedFiberBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedFiberBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberBassSeed f T) i

/-- The unchanged finite ambient transition is the original iterated ambient seed. -/
def boundedFlatCoefficientSupportedAmbientBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedFlatCoefficientSupportedAmbientBassDiagram T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedAmbientBassSeed T) i

/-- The original supported inclusion at every unchanged finite Bass stage. -/
def boundedFlatCoefficientSupportedFiberBassForget (i : ℕ) :
    boundedFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedAmbientBassDiagram T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)

/-- The original ambient change to coarse relative-open weakness at every finite stage. -/
def boundedFlatCoefficientSupportedAmbientBassOpen (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedFlatCoefficientSupportedOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)

/-- The actual original supported inclusion commutes with every unchanged seed transition. -/
theorem boundedFlatCoefficientSupportedFiberBassForget_transition (i : ℕ) :
    boundedFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedFlatCoefficientSupportedAmbientBassTransition T i =
      boundedFlatCoefficientSupportedFiberBassTransition f T i ≫
        boundedFlatCoefficientSupportedFiberBassForget f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberBassSeed f T)
      (boundedFlatCoefficientSupportedAmbientBassSeed T)
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedFiberBassSeed_forget f T) i).symm

omit [IsOpenImmersion f.left] in
/-- The same original fine-to-coarse map commutes with every actual finite transition. -/
theorem boundedFlatCoefficientSupportedAmbientBassOpen_transition (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassOpen f T i ≫
      boundedFlatCoefficientSupportedOpenBassTransition f T i =
      boundedFlatCoefficientSupportedAmbientBassTransition T i ≫
        boundedFlatCoefficientSupportedAmbientBassOpen f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedAmbientBassSeed T) (boundedFlatCoefficientSupportedOpenBassSeed
      f T)
    (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedAmbientBassSeed_open f T) i).symm

/-- Iterate precisely the same original coefficient-natural whole supported localization null. -/
def boundedFlatCoefficientSupportedFiberBassOpenNull (i : ℕ) :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedFiberBassForget f T i)
      (boundedFlatCoefficientSupportedAmbientBassOpen f T i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T) i

/-- All original null times preserve every unchanged finite supported/open transition. -/
theorem boundedFlatCoefficientSupportedFiberBassOpenNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedFlatCoefficientSupportedOpenBassTransition f T i).app a).map m
        (((boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m (s, x)) =
      ((boundedFlatCoefficientSupportedFiberBassOpenNull f T (i + 1)).homotopy a).level m
        (s, ((boundedFlatCoefficientSupportedFiberBassTransition f T i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T)
    (boundedFlatCoefficientSupportedFiberBassSeed f T) (boundedFlatCoefficientSupportedOpenBassSeed
      f T)
    (fun s ↦ boundedFlatCoefficientSupportedFiberOpenNullTimeSlice_seed f T s) i a m s x).symm

/-- Actual finite cone descent along the unchanged complete iterated supported localization null. -/
def boundedFlatCoefficientSupportedFiberBassOpenConeMap (i : ℕ) :
    mappingConeDiagram (boundedFlatCoefficientSupportedFiberBassForget f T i) ⟶
      boundedFlatCoefficientSupportedOpenBassDiagram f T i :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedFiberBassForget f T i)
    (boundedFlatCoefficientSupportedAmbientBassOpen f T i)
    (boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy
    (boundedFlatCoefficientSupportedFiberBassOpenNull f T i).naturality

/-- Every original ambient inclusion face is exactly the original finite fine-to-coarse map. -/
theorem boundedFlatCoefficientSupportedFiberBassOpenConeMap_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedFiberBassForget f T i).app a) ≫
        (boundedFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a =
      (boundedFlatCoefficientSupportedAmbientBassOpen f T i).app a := mappingConeInclusion_desc _ _
        _

/-- Actual finite Model excision propagates stability of the original initial support cone. -/
theorem boundedFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberModelFunctor f T)
      (boundedFlatCoefficientSupportedAmbientModelFunctor T)
    (boundedFlatCoefficientSupportedOpenModelFunctor f T)
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T)
    (fun a ↦ boundedFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T a) i a

/-- Genuine finite Model growth supplies signed excision for the original supported inclusion. -/
theorem boundedFlatCoefficientSupportedFiberBassForget_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientSupportedFiberBassForget f T i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFiberModelFunctor f T)
      (boundedFlatCoefficientSupportedAmbientModelFunctor T)
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) i a


end Quillen.PerfectComplexes
