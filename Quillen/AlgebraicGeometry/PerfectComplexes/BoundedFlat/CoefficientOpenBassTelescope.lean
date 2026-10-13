/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassTower
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap
public import Quillen.Topology.Prespectrum.TelescopeConeDescentStable
public import Quillen.Topology.Prespectrum.TelescopeStableRepresentability
public import Quillen.Topology.Prespectrum.ConeStableVanishing

/-!
# Original global C/F/G completion and actual stable restriction

The original finite stages and transitions determine the actual coefficient
telescopes and unchanged r-infinity/q-infinity maps. Whole finite localization
null transition equations construct the same complete telescope null, with
localization-null time and telescope height independent.

Actual finite Model cone descent and excision pass to this original telescope
cone. The constructed graded transition nulls kill all signed telescope classes
via finite representatives. Its unchanged cone therefore vanishes, proving the
actual coarse-to-fine restriction stable in every integer degree. No uniform
whole-telescope connectivity or classical K-theory comparison is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original C completion, with its unchanged finite stages and original transitions. -/
def boundedFlatCoefficientOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientOpenBassDiagram f)
    (boundedFlatCoefficientOpenBassTransition f)

/-- Original F completion of the actual native fine open row. -/
def boundedFlatCoefficientFullOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientFullOpenBassDiagram f)
    (boundedFlatCoefficientFullOpenBassTransition f)

/-- Original coefficient-natural r-infinity retaining all finite restriction components. -/
def boundedFlatCoefficientOpenBassTelescopeRestriction :
    boundedFlatCoefficientOpenBassTelescopeFunctor f ⟶
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedFlatCoefficientOpenBassDiagram f)
    (boundedFlatCoefficientFullOpenBassDiagram f) (boundedFlatCoefficientOpenBassTransition f)
    (boundedFlatCoefficientFullOpenBassTransition f) (boundedFlatCoefficientOpenBassRestriction f)
    (boundedFlatCoefficientOpenBassRestriction_transition f)

/-- Original C stage inclusions with the same initial cylinder faces. -/
def boundedFlatCoefficientOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientOpenBassDiagram f i ⟶ boundedFlatCoefficientOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedFlatCoefficientOpenBassDiagram f)
    (boundedFlatCoefficientOpenBassTransition f) i

/-- Original F stage inclusions with the same initial cylinder faces. -/
def boundedFlatCoefficientFullOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedFlatCoefficientFullOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedFlatCoefficientFullOpenBassDiagram f)
    (boundedFlatCoefficientFullOpenBassTransition f) i

/-- The original restriction retains every finite inclusion face. -/
theorem boundedFlatCoefficientOpenBassTelescopeInclusion_restriction (i : ℕ) :
    boundedFlatCoefficientOpenBassTelescopeInclusion f i ≫
        boundedFlatCoefficientOpenBassTelescopeRestriction f =
      boundedFlatCoefficientOpenBassRestriction f i ≫
        boundedFlatCoefficientFullOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original G completion with the exact original graded seeds and transitions. -/
def boundedFlatCoefficientGradedOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientGradedOpenBassDiagram f)
    (boundedFlatCoefficientGradedOpenBassTransition f)

/-- Original coefficient-natural q-infinity retaining all finite grading components. -/
def boundedFlatCoefficientOpenBassTelescopeGrading :
    boundedFlatCoefficientFullOpenBassTelescopeFunctor f ⟶
      boundedFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedFlatCoefficientFullOpenBassDiagram f)
    (boundedFlatCoefficientGradedOpenBassDiagram f) (boundedFlatCoefficientFullOpenBassTransition f)
    (boundedFlatCoefficientGradedOpenBassTransition f) (boundedFlatCoefficientOpenBassGrading f)
    (boundedFlatCoefficientOpenBassGrading_transition f)

/-- Original G stage inclusions with their unchanged initial cylinder faces. -/
def boundedFlatCoefficientGradedOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientGradedOpenBassDiagram f i ⟶
      boundedFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedFlatCoefficientGradedOpenBassDiagram f)
    (boundedFlatCoefficientGradedOpenBassTransition f) i

/-- The original grading retains every finite inclusion face. -/
theorem boundedFlatCoefficientOpenBassTelescopeInclusion_grading (i : ℕ) :
    boundedFlatCoefficientFullOpenBassTelescopeInclusion f i ≫
        boundedFlatCoefficientOpenBassTelescopeGrading f =
      boundedFlatCoefficientOpenBassGrading f i ≫
        boundedFlatCoefficientGradedOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
def boundedFlatCoefficientOpenBassTelescopeGradingNull :
    DiagramNullHomotopy (boundedFlatCoefficientOpenBassTelescopeRestriction f)
      (boundedFlatCoefficientOpenBassTelescopeGrading f) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientGradedOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientGradedOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassGrading f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientOpenBassRestriction_transition f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientOpenBassGrading_transition f i))
    (fun i ↦ (boundedFlatCoefficientOpenBassGradingNull f i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientOpenBassGradingNull_transition f i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientGradedOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedFlatCoefficientGradedOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientGradedOpenBassDiagram f z.1).map g).map m
            (((boundedFlatCoefficientOpenBassGradingNull f z.1).homotopy a).level m (s, z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientGradedOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedFlatCoefficientGradedOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientOpenBassGradingNull f z.1).homotopy b).level m
            (s, ((boundedFlatCoefficientOpenBassDiagram f z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedFlatCoefficientGradedOpenBassDiagram f i).obj b)
        (fun i ↦ (boundedFlatCoefficientGradedOpenBassTransition f i).app b) m z.1 (z.2.1, y))
        ((boundedFlatCoefficientOpenBassGradingNull f z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
theorem boundedFlatCoefficientOpenBassTelescopeGradingNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedFlatCoefficientOpenBassTelescopeGradingNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedFlatCoefficientOpenBassDiagram f k).obj a)
        (fun k ↦ (boundedFlatCoefficientOpenBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedFlatCoefficientGradedOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedFlatCoefficientGradedOpenBassTransition f k).app a) m i
        (t, ((boundedFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) := rfl

/-- Actual whole transition nulls kill every original G stage-inclusion stable map. -/
theorem boundedFlatCoefficientGradedOpenBassTelescopeInclusion_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatCoefficientGradedOpenBassTelescopeInclusion f i).app a) = 0 := by
  let E := fun k ↦ (boundedFlatCoefficientGradedOpenBassDiagram f k).obj a
  let τ := fun k ↦ (boundedFlatCoefficientGradedOpenBassTransition f k).app a
  change (stableHomotopyFunctor d).map (Telescope.inclusion E τ i) = 0
  have hi := Telescope.inclusion_transition_stableMap E τ (Nat.le_succ i) d
  rw [Telescope.transition_succ] at hi
  have hz : (stableHomotopyFunctor d).map (τ i) = 0 :=
    boundedFlatCoefficientGradedOpenBassTransition_stableMap_eq_zero f i a d
  exact hi.trans (by rw [hz, CategoryTheory.Limits.zero_comp])

/-- Finite original stable representatives prove G-infinity vanishes in every integer degree. -/
theorem boundedFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a) d) :
    x = 0 := by
  let E := fun k ↦ (boundedFlatCoefficientGradedOpenBassDiagram f k).obj a
  let τ := fun k ↦ (boundedFlatCoefficientGradedOpenBassTransition f k).app a
  let : ∀ i n, T1Space ((E i).space n) :=
    fun i n ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientGradedOpenModelFunctor f) a n
  obtain ⟨i, y, hy⟩ := Telescope.exists_stable_representative E τ d x
  have hi := boundedFlatCoefficientGradedOpenBassTelescopeInclusion_stableMap_eq_zero f i a d
  exact hy.symm.trans ((ConcreteCategory.congr_hom hi y).trans rfl)

/-- The actual signed G-infinity groups are subsingletons. -/
theorem boundedFlatCoefficientGradedOpenBassTelescope_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      ((boundedFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a) d) :=
  ⟨fun x y ↦ (boundedFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d x).trans
    (boundedFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d y).symm⟩

/-- The original telescope cone descends with precisely the same complete N-infinity. -/
def boundedFlatCoefficientOpenBassTelescopeConeComparison :
    mappingConeDiagram (boundedFlatCoefficientOpenBassTelescopeRestriction f) ⟶
      boundedFlatCoefficientGradedOpenBassTelescopeFunctor f :=
  mappingConeDescTransformation (boundedFlatCoefficientOpenBassTelescopeRestriction f)
    (boundedFlatCoefficientOpenBassTelescopeGrading f)
    (boundedFlatCoefficientOpenBassTelescopeGradingNull f).homotopy
    (boundedFlatCoefficientOpenBassTelescopeGradingNull f).naturality

/-- The original telescope cone inclusion has exactly q-infinity as its face. -/
theorem boundedFlatCoefficientOpenBassTelescopeConeComparison_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) ≫
        (boundedFlatCoefficientOpenBassTelescopeConeComparison f).app a =
      (boundedFlatCoefficientOpenBassTelescopeGrading f).app a := mappingConeInclusion_desc _ _ _

omit [CompactSpace P.left] [CompactSpace Q.left] in
/-- Genuine finite Model excision supplies the original telescope cone-to-fiber comparison. -/
theorem boundedFlatCoefficientOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientFullOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientFullOpenModelFunctor f) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientOpenBassRestriction_transition f i))
    (fun i ↦ boundedFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence f i a)

variable [QuasiSeparatedSpace Q.left]

/-- Actual finite cone stability passes to the same original telescope descent. -/
theorem boundedFlatCoefficientOpenBassTelescopeConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientOpenBassTelescopeConeComparison f).app a) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientFullOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientFullOpenModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientGradedOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientGradedOpenModelFunctor f) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientFullOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientGradedOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedFlatCoefficientGradedOpenBassTransition f i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassRestriction f i).app a)
    (fun i ↦ (boundedFlatCoefficientOpenBassGrading f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientOpenBassRestriction_transition f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientOpenBassGrading_transition f i))
    (fun i ↦ (boundedFlatCoefficientOpenBassGradingNull f i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientOpenBassGradingNull_transition f i a m s x)
    (fun i ↦ boundedFlatCoefficientOpenBassConeComparison_isStableEquivalence f i a)

/-- The same original restriction cone has no signed stable classes. -/
theorem boundedFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)) d) := by
  let j := (stableHomotopyFunctor d).map
    ((boundedFlatCoefficientOpenBassTelescopeConeComparison f).app a)
  have hi : Function.Injective j :=
    ((ConcreteCategory.isIso_iff_bijective j).mp
      (boundedFlatCoefficientOpenBassTelescopeConeComparison_isStableEquivalence f a d)).injective
  exact ⟨fun x y ↦ hi
    ((boundedFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d (j x)).trans
      (boundedFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d (j y)).symm)⟩

/-- The actual original r-infinity is stable in every integer degree. -/
theorem boundedFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) :=
  isStableEquivalence_of_cone_stableGroup_subsingleton _
    (boundedFlatCoefficientOpenBassTelescopeRestriction_coneFiber_isStableEquivalence f a)
    (boundedFlatCoefficientOpenBassTelescopeRestriction_cone_stableGroup_subsingleton f a)

end Quillen.PerfectComplexes
