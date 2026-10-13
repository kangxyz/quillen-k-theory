/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberBassTower
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassTelescope

/-!
# Original auxiliary intersection-support telescope cone and coarse completion

Original fiber and auxiliary ambient finite stages and seeds define the literal
native telescopes. Their unchanged inclusion and identity weakness change carry
the whole null from the same finite supported localization nulls. Genuine finite
Model excision and cone stability pass to this original telescope cone. Null
time and telescope height remain independent on every original cylinder.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original supported completion with its unchanged native finite stages and seeds. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedFlatCoefficientSupportedFiberBassTransition f T)

/-- Original native fine ambient completion with its unchanged finite stages and seeds. -/
def boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedFlatCoefficientSupportedAmbientBassTransition T)

/-- The original coefficient-natural supported-forget telescope map. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeForget :
    boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T ⟶
      boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T :=
  Telescope.diagramMap (boundedFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedFlatCoefficientSupportedAmbientBassDiagram T)
      (boundedFlatCoefficientSupportedFiberBassTransition f T)
    (boundedFlatCoefficientSupportedAmbientBassTransition T)
      (boundedFlatCoefficientSupportedFiberBassForget f T)
    (boundedFlatCoefficientSupportedFiberBassForget_transition f T)

/-- The original ambient-to-coarse telescope map with all original finite components. -/
def boundedFlatCoefficientSupportedAmbientBassTelescopeOpen :
    boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T ⟶
      boundedFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedFlatCoefficientSupportedOpenBassDiagram f T)
      (boundedFlatCoefficientSupportedAmbientBassTransition T)
    (boundedFlatCoefficientSupportedOpenBassTransition f T)
      (boundedFlatCoefficientSupportedAmbientBassOpen f T)
    (boundedFlatCoefficientSupportedAmbientBassOpen_transition f T)

/-- The original supported finite-stage inclusions into its completion. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedFlatCoefficientSupportedFiberBassTransition f T) i

/-- The original ambient finite-stage inclusions into its completion. -/
def boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedFlatCoefficientSupportedAmbientBassTransition T) i

/-- The original supported-forget telescope map retains every unchanged inclusion face. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeInclusion_forget (i : ℕ) :
    boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T i ≫
        boundedFlatCoefficientSupportedFiberBassTelescopeForget f T =
      boundedFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

omit [IsOpenImmersion f.left] in
/-- Original fine-to-coarse completion retains every unchanged ambient stage inclusion. -/
theorem boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion_open (i : ℕ) :
    boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T =
      boundedFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T)
      (boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassOpen f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedAmbientBassOpen_transition f
      T i))
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedFiberBassOpenNull_transition f T i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientSupportedOpenBassDiagram f T z.1).map g).map m
            (((boundedFlatCoefficientSupportedFiberBassOpenNull f T z.1).homotopy a).level m (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientSupportedFiberBassOpenNull f T z.1).homotopy b).level m
            (s, ((boundedFlatCoefficientSupportedFiberBassDiagram f T z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
        (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1 (z.2.1, y))
        ((boundedFlatCoefficientSupportedFiberBassOpenNull f T z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedFlatCoefficientSupportedFiberBassDiagram f T k).obj a)
        (fun k ↦ (boundedFlatCoefficientSupportedFiberBassTransition f T k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T k).obj a)
      (fun k ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T k).app a) m i
        (t, ((boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m (s, x)) :=
          rfl

/-- The original supported telescope cone descends using precisely the same complete null. -/
def boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap :
    mappingConeDiagram (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T) ⟶
      boundedFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T)
    (boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T)
    (boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy
    (boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).naturality

/-- The original ambient inclusion face is exactly the original ambient-to-coarse completion. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a) ≫
        (boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a =
      (boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a :=
        mappingConeInclusion_desc _ _ _

/-- Actual finite Model excision supplies the original supported telescope cone-fiber comparison. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedFiberModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedAmbientBassDiagram T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedAmbientModelFunctor T) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ boundedFlatCoefficientSupportedFiberBassForget_coneFiber_isStableEquivalence f T i a)

/-- The original supported telescope cone descent is stable in every signed degree. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a)
      := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedFiberModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedAmbientBassDiagram T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedAmbientModelFunctor T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedOpenModelFunctor f T) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedAmbientBassOpen f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedAmbientBassOpen_transition f
      T i))
    (fun i ↦ (boundedFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedFiberBassOpenNull_transition f T i a m s x)
    (fun i ↦ boundedFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence f T i a)

/-- The actual signed coarse boundary uses the original inclusion and this same whole null. -/
theorem boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a) ≫
      stableFiberConnecting ((boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a) d
        =
    stableMappingConeConnecting ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app
      a)
      (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a)
        d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a)
          ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
          ((boundedFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a) d


end Quillen.PerfectComplexes
