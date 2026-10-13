/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassTelescope

/-!
# The original global supported telescope cone and coarse completion

The original finite stages and seeds define the supported and ambient native
coefficient telescopes. Their unchanged inclusion and change-of-weakness maps
carry the whole telescope null of the same finite localization nulls. Genuine
finite Model excision and cone stability pass to this original telescope cone,
without any uniform telescope connectivity or finite seed-stabilization premise.
Null time and telescope height remain independent on every original cylinder.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original supported completion with its unchanged native finite stages and seeds. -/
def boundedFlatCoefficientSupportedBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedBassDiagram f)
    (boundedFlatCoefficientSupportedBassTransition f)

/-- Original native fine ambient completion with its unchanged finite stages and seeds. -/
def boundedFlatCoefficientAmbientBassTelescopeFunctor (Q : Over (Spec R)) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientAmbientBassDiagram Q)
    (boundedFlatCoefficientAmbientBassTransition Q)

/-- The original coefficient-natural supported-forget telescope map. -/
def boundedFlatCoefficientSupportedBassTelescopeForget :
    boundedFlatCoefficientSupportedBassTelescopeFunctor f ⟶
      boundedFlatCoefficientAmbientBassTelescopeFunctor Q :=
  Telescope.diagramMap (boundedFlatCoefficientSupportedBassDiagram f)
    (boundedFlatCoefficientAmbientBassDiagram Q) (boundedFlatCoefficientSupportedBassTransition f)
    (boundedFlatCoefficientAmbientBassTransition Q) (boundedFlatCoefficientSupportedBassForget f)
    (boundedFlatCoefficientSupportedBassForget_transition f)

/-- The original ambient-to-coarse telescope map with all original finite components. -/
def boundedFlatCoefficientAmbientBassTelescopeOpen :
    boundedFlatCoefficientAmbientBassTelescopeFunctor Q ⟶
      boundedFlatCoefficientOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedFlatCoefficientAmbientBassDiagram Q)
    (boundedFlatCoefficientOpenBassDiagram f) (boundedFlatCoefficientAmbientBassTransition Q)
    (boundedFlatCoefficientOpenBassTransition f) (boundedFlatCoefficientAmbientBassOpen f)
    (boundedFlatCoefficientAmbientBassOpen_transition f)

/-- The original supported finite-stage inclusions into its completion. -/
def boundedFlatCoefficientSupportedBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedBassDiagram f i ⟶
      boundedFlatCoefficientSupportedBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedBassDiagram f)
    (boundedFlatCoefficientSupportedBassTransition f) i

/-- The original ambient finite-stage inclusions into its completion. -/
def boundedFlatCoefficientAmbientBassTelescopeInclusion (Q : Over (Spec R)) (i : ℕ) :
    boundedFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedFlatCoefficientAmbientBassTelescopeFunctor Q :=
  Telescope.diagramInclusion (boundedFlatCoefficientAmbientBassDiagram Q)
    (boundedFlatCoefficientAmbientBassTransition Q) i

/-- The original supported-forget telescope map retains every unchanged inclusion face. -/
theorem boundedFlatCoefficientSupportedBassTelescopeInclusion_forget (i : ℕ) :
    boundedFlatCoefficientSupportedBassTelescopeInclusion f i ≫
        boundedFlatCoefficientSupportedBassTelescopeForget f =
      boundedFlatCoefficientSupportedBassForget f i ≫
        boundedFlatCoefficientAmbientBassTelescopeInclusion Q i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Original fine-to-coarse completion retains every unchanged ambient stage inclusion. -/
theorem boundedFlatCoefficientAmbientBassTelescopeInclusion_open (i : ℕ) :
    boundedFlatCoefficientAmbientBassTelescopeInclusion Q i ≫
        boundedFlatCoefficientAmbientBassTelescopeOpen f =
      boundedFlatCoefficientAmbientBassOpen f i ≫
        boundedFlatCoefficientOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
def boundedFlatCoefficientSupportedBassTelescopeOpenNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedBassTelescopeForget f)
      (boundedFlatCoefficientAmbientBassTelescopeOpen f) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassOpen f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedBassForget_transition f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientAmbientBassOpen_transition f i))
    (fun i ↦ (boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedBassOpenNull_transition f i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientOpenBassDiagram f z.1).map g).map m
            (((boundedFlatCoefficientSupportedBassOpenNull f z.1).homotopy a).level m (s, z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientSupportedBassOpenNull f z.1).homotopy b).level m
            (s, ((boundedFlatCoefficientSupportedBassDiagram f z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj b)
        (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app b) m z.1 (z.2.1, y))
        ((boundedFlatCoefficientSupportedBassOpenNull f z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
theorem boundedFlatCoefficientSupportedBassTelescopeOpenNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedFlatCoefficientSupportedBassDiagram f k).obj a)
        (fun k ↦ (boundedFlatCoefficientSupportedBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedFlatCoefficientOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedFlatCoefficientOpenBassTransition f k).app a) m i
        (t, ((boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) := rfl

/-- The original supported telescope cone descends using precisely the same complete null. -/
def boundedFlatCoefficientSupportedBassTelescopeOpenConeMap :
    mappingConeDiagram (boundedFlatCoefficientSupportedBassTelescopeForget f) ⟶
      boundedFlatCoefficientOpenBassTelescopeFunctor f :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedBassTelescopeForget f)
    (boundedFlatCoefficientAmbientBassTelescopeOpen f)
    (boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy
    (boundedFlatCoefficientSupportedBassTelescopeOpenNull f).naturality

/-- The original ambient inclusion face is exactly the original ambient-to-coarse completion. -/
theorem boundedFlatCoefficientSupportedBassTelescopeOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
        (boundedFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a =
      (boundedFlatCoefficientAmbientBassTelescopeOpen f).app a := mappingConeInclusion_desc _ _ _

/-- Actual finite Model excision supplies the original supported telescope cone-fiber comparison. -/
theorem boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientAmbientBassDiagram Q i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSectionModelRow Q) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedBassForget_transition f i))
    (fun i ↦ boundedFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f i a)

/-- The original supported telescope cone descent is stable in every signed degree. -/
theorem boundedFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientAmbientBassDiagram Q i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSectionModelRow Q) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientOpenModelFunctor f) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ (boundedFlatCoefficientAmbientBassOpen f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedBassForget_transition f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientAmbientBassOpen_transition f i))
    (fun i ↦ (boundedFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedBassOpenNull_transition f i a m s x)
    (fun i ↦ boundedFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f i a)

/-- The actual signed coarse boundary uses the original inclusion and this same whole null. -/
theorem boundedFlatCoefficientSupportedBassTelescopeOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedFlatCoefficientAmbientBassTelescopeOpen f).app a) d =
    stableMappingConeConnecting ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedFlatCoefficientAmbientBassTelescopeOpen f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d

end Quillen.PerfectComplexes
