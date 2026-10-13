/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassTower
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap
public import Quillen.Topology.Prespectrum.TelescopeConeDescentStable
public import Quillen.Topology.Prespectrum.TelescopeStableRepresentability
public import Quillen.Topology.Prespectrum.ConeStableVanishing

/-!
# Original auxiliary-supported C_Z/F_Z/G_Z completion and actual stable restriction

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
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original C completion, with its unchanged finite stages and original transitions. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedOpenBassTransition f T)

/-- Original F completion of the actual auxiliary-supported native fine open row. -/
def boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedFullOpenBassTransition f T)

/-- Original coefficient-natural r-infinity retaining all finite restriction components. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeRestriction :
    boundedFlatCoefficientSupportedOpenBassTelescopeFunctor f T ⟶
      boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedFullOpenBassDiagram f T)
      (boundedFlatCoefficientSupportedOpenBassTransition f T)
    (boundedFlatCoefficientSupportedFullOpenBassTransition f T)
      (boundedFlatCoefficientSupportedOpenBassRestriction f T)
    (boundedFlatCoefficientSupportedOpenBassRestriction_transition f T)

/-- Original C stage inclusions with the same initial cylinder faces. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedOpenBassTransition f T) i

/-- Original F stage inclusions with the same initial cylinder faces. -/
def boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedFullOpenBassTransition f T) i

omit [IsOpenImmersion f.left] in
/-- The original restriction retains every finite inclusion face. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeInclusion_restriction (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T i ≫
        boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T =
      boundedFlatCoefficientSupportedOpenBassRestriction f T i ≫
        boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original G completion with the exact original graded seeds and transitions. -/
def boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1}
  :=
  Telescope.diagramFunctor (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedGradedOpenBassTransition f T)

/-- Original coefficient-natural q-infinity retaining all finite grading components. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeGrading :
    boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T ⟶
      boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T)
      (boundedFlatCoefficientSupportedFullOpenBassTransition f T)
    (boundedFlatCoefficientSupportedGradedOpenBassTransition f T)
      (boundedFlatCoefficientSupportedOpenBassGrading f T)
    (boundedFlatCoefficientSupportedOpenBassGrading_transition f T)

/-- Original G stage inclusions with their unchanged initial cylinder faces. -/
def boundedFlatCoefficientSupportedGradedOpenBassTelescopeInclusion (i : ℕ) :
    boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T)
    (boundedFlatCoefficientSupportedGradedOpenBassTransition f T) i

/-- The original grading retains every finite inclusion face. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeInclusion_grading (i : ℕ) :
    boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i ≫
        boundedFlatCoefficientSupportedOpenBassTelescopeGrading f T =
      boundedFlatCoefficientSupportedOpenBassGrading f T i ≫
        boundedFlatCoefficientSupportedGradedOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeGradingNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T)
      (boundedFlatCoefficientSupportedOpenBassTelescopeGrading f T) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassGrading f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedOpenBassGrading_transition f
      T i))
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedOpenBassGradingNull_transition f T i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientSupportedGradedOpenBassDiagram f T z.1).map g).map m
            (((boundedFlatCoefficientSupportedOpenBassGradingNull f T z.1).homotopy a).level m (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedFlatCoefficientSupportedOpenBassGradingNull f T z.1).homotopy b).level m
            (s, ((boundedFlatCoefficientSupportedOpenBassDiagram f T z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
        (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, y))
        ((boundedFlatCoefficientSupportedOpenBassGradingNull f T z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeGradingNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T k).obj a)
        (fun k ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a)
      (fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T k).app a) m i
        (t, ((boundedFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m (s, x))
          := rfl

/-- Actual whole transition nulls kill every original G stage-inclusion stable map. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassTelescopeInclusion_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedGradedOpenBassTelescopeInclusion f T i).app a) = 0 := by
  let E := fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a
  let τ := fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T k).app a
  change (stableHomotopyFunctor d).map (Telescope.inclusion E τ i) = 0
  have hi := Telescope.inclusion_transition_stableMap E τ (Nat.le_succ i) d
  rw [Telescope.transition_succ] at hi
  have hz : (stableHomotopyFunctor d).map (τ i) = 0 :=
    boundedFlatCoefficientSupportedGradedOpenBassTransition_stableMap_eq_zero f T i a d
  exact hi.trans (by rw [hz, CategoryTheory.Limits.zero_comp])

/-- Finite original stable representatives prove G-infinity vanishes in every integer degree. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f
      T).obj a) d) :
    x = 0 := by
  let E := fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a
  let τ := fun k ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T k).app a
  let : ∀ i n, T1Space ((E i).space n) :=
    fun i n ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T) a n
  obtain ⟨i, y, hy⟩ := Telescope.exists_stable_representative E τ d x
  have hi := boundedFlatCoefficientSupportedGradedOpenBassTelescopeInclusion_stableMap_eq_zero f T i
    a d
  exact hy.symm.trans ((ConcreteCategory.congr_hom hi y).trans rfl)

/-- The actual signed G-infinity groups are subsingletons. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      ((boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T).obj a) d) :=
  ⟨fun x y ↦ (boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d
    x).trans
    (boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d y).symm⟩

/-- The original telescope cone descends with precisely the same complete N-infinity. -/
def boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison :
    mappingConeDiagram (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T) ⟶
      boundedFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T)
    (boundedFlatCoefficientSupportedOpenBassTelescopeGrading f T)
    (boundedFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).homotopy
    (boundedFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).naturality

/-- The original telescope cone inclusion has exactly q-infinity as its face. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) ≫
        (boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a =
      (boundedFlatCoefficientSupportedOpenBassTelescopeGrading f T).app a :=
        mappingConeInclusion_desc _ _ _

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left] in
/-- Genuine finite Model excision supplies the original telescope cone-to-fiber comparison. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)) := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a).space m)
    :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ boundedFlatCoefficientSupportedOpenBassRestriction_coneFiber_isStableEquivalence f T i
      a)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Actual finite cone stability passes to the same original telescope descent. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a)
      := by
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a).space m)
    :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassGrading f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedFlatCoefficientSupportedOpenBassGrading_transition f
      T i))
    (fun i ↦ (boundedFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a)
    (fun i m s x ↦ boundedFlatCoefficientSupportedOpenBassGradingNull_transition f T i a m s x)
    (fun i ↦ boundedFlatCoefficientSupportedOpenBassConeComparison_isStableEquivalence f T i a)

/-- The same original restriction cone has no signed stable classes. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)) d) :=
        by
  let j := (stableHomotopyFunctor d).map
    ((boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a)
  have hi : Function.Injective j :=
    ((ConcreteCategory.isIso_iff_bijective j).mp
      (boundedFlatCoefficientSupportedOpenBassTelescopeConeComparison_isStableEquivalence f T a
        d)).injective
  exact ⟨fun x y ↦ hi
    ((boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d (j
      x)).trans
      (boundedFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d (j
        y)).symm)⟩

/-- The actual original r-infinity is stable in every integer degree. -/
theorem boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) :=
  isStableEquivalence_of_cone_stableGroup_subsingleton _
    (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_coneFiber_isStableEquivalence f T
      a)
    (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction_cone_stableGroup_subsingleton f T
      a)

end Quillen.PerfectComplexes
