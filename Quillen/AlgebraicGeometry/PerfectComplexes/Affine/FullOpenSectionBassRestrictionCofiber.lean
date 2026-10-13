/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassRestrictionTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassGradingTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionGradingNullBassSeed
public import Quillen.KTheory.Bass.StrictDiagramIterateNullTimeSlice
public import Quillen.Topology.Prespectrum.TelescopeConeDescentStable
public import Quillen.Topology.Prespectrum.ConeStableVanishing

/-!
# The original full-open restriction cofiber on the Bass telescopes

The constructed canonical null preserves the original Bass seeds at every null time.
Its unchanged finite iterates therefore give the whole compatible telescope null. The
actual finite Model cone comparisons pass to the same telescope descent. The original
graded telescope has zero signed stable groups, so the unchanged coarse-to-full restriction
is stable in every integer degree. Compactness of the original open is the only extra
geometric premise; no classical stabilization or identification is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original finite localization null preserves each actual transition at the same time. -/
theorem boundedFlatAffineSectionFullOpenBassRestrictionGradingNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineFullOpenGradedSectionBassTransition j i).app a).map m
        (((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).homotopy a).level m
          (s, x)) =
      ((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j (i + 1)).homotopy a).level m
        (s, ((boundedFlatAffineSectionOpenBassTransition j i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j)
    (boundedFlatAffineSectionOpenBassSeed j)
    (boundedFlatAffineFullOpenGradedSectionBassSeed j)
    (fun s ↦ boundedFlatAffineFullOpenSectionGradingNullTimeSlice_seed j s)
    i a m s x).symm

/-- The telescope retains the same entire canonical null and the original finite transitions. -/
def boundedFlatAffineSectionFullOpenBassTelescopeGradingNull :
    DiagramNullHomotopy (boundedFlatAffineSectionFullOpenBassTelescopeRestriction j)
      (boundedFlatAffineFullOpenSectionBassTelescopeGrading j) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedFlatAffineSectionOpenBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineSectionOpenBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineSectionFullOpenBassRestriction j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassGrading j i).app a)
    (fun i ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSectionFullOpenBassRestriction_transition j i))
    (fun i ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineFullOpenSectionBassGrading_transition j i))
    (fun i ↦ (boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).homotopy a)
    (fun i m s x ↦ boundedFlatAffineSectionFullOpenBassRestrictionGradingNull_transition
      j i a m s x)
  naturality {a b} f m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj b)
          (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app b) m z.1
          (z.2.1, ((boundedFlatAffineFullOpenGradedSectionBassDiagram j z.1).map f).map m
            (((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j z.1).homotopy a).level m
              (s, z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj b)
          (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app b) m z.1
          (z.2.1,
            ((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j z.1).homotopy b).level m
            (s, ((boundedFlatAffineSectionOpenBassDiagram j z.1).map f).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj b)
        (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app b)
        m z.1 (z.2.1, y))
        ((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j z.1).naturality f m s z.2.2)

/-- Localization-null time and telescope height are independent original coordinates. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeGradingNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineSectionFullOpenBassTelescopeGradingNull j).homotopy a).level m
        (s, Telescope.cylinder
          (fun i ↦ (boundedFlatAffineSectionOpenBassDiagram j i).obj a)
          (fun i ↦ (boundedFlatAffineSectionOpenBassTransition j i).app a) m i (t, x)) =
      Telescope.cylinder
        (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj a)
        (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app a) m i
        (t, ((boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).homotopy a).level m
          (s, x)) := rfl

/-- The original telescope restriction cone descends using this same constructed null. -/
def boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap :
    mappingConeDiagram (boundedFlatAffineSectionFullOpenBassTelescopeRestriction j) ⟶
      boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j :=
  mappingConeDescTransformation (boundedFlatAffineSectionFullOpenBassTelescopeRestriction j)
    (boundedFlatAffineFullOpenSectionBassTelescopeGrading j)
    (boundedFlatAffineSectionFullOpenBassTelescopeGradingNull j).homotopy
    (boundedFlatAffineSectionFullOpenBassTelescopeGradingNull j).naturality

/-- The target face remains the actual fine-to-graded telescope arrow. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a) ≫
        (boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap j).app a =
      (boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app a :=
  mappingConeInclusion_desc _ _ _

/-- Actual finite Model cone descents pass to the unchanged telescope cone descent. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence
      ((boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap j).app a) := by
  let : ∀ i m, T1Space (((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineSectionOpenModelFunctor j) a m
  let : ∀ i m, T1Space (((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineFullOpenSectionModelFunctor j) a m
  let : ∀ i m, T1Space (((boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineFullOpenGradedSectionModelFunctor j) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedFlatAffineSectionOpenBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineSectionOpenBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineSectionFullOpenBassRestriction j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassGrading j i).app a)
    (fun i ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSectionFullOpenBassRestriction_transition j i))
    (fun i ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineFullOpenSectionBassGrading_transition j i))
    (fun i ↦ (boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).homotopy a)
    (fun i m s x ↦ boundedFlatAffineSectionFullOpenBassRestrictionGradingNull_transition
      j i a m s x)
    (fun i ↦ boundedFlatAffineSectionFullOpenBassGradingConeMap_isStableEquivalence j i a)

omit [CompactSpace U] in
/-- Genuine finite Model excision supplies the original telescope cone-to-fiber comparison. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a)) := by
  let : ∀ i m, T1Space (((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineSectionOpenModelFunctor j) a m
  let : ∀ i m, T1Space (((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatAffineFullOpenSectionModelFunctor j) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedFlatAffineSectionOpenBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineSectionOpenBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassDiagram j i).obj a)
    (fun i ↦ (boundedFlatAffineFullOpenSectionBassTransition j i).app a)
    (fun i ↦ (boundedFlatAffineSectionFullOpenBassRestriction j i).app a)
    (fun i ↦ congrArg (fun f ↦ f.app a)
      (boundedFlatAffineSectionFullOpenBassRestriction_transition j i))
    (fun i ↦ boundedFlatAffineSectionFullOpenBassRestriction_coneFiber_isStableEquivalence j i a)

/-- The original cone has zero stable groups because its constructed graded comparison is stable. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
    (a : Under R) (d : ℤ) :
    Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a)) d) := by
  let f := (stableHomotopyFunctor d).map
    ((boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap j).app a)
  let := boundedFlatAffineSectionFullOpenBassTelescopeGradingConeMap_isStableEquivalence j a d
  have hinj : Function.Injective f.hom :=
    ((ConcreteCategory.isIso_iff_bijective f).mp inferInstance).1
  exact ⟨fun x y ↦ hinj
    ((boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d (f x)).trans
      (boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d (f y)).symm)⟩

/-- The actual coarse-to-full section telescope restriction is stable in every integer degree. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeRestriction_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a) :=
  isStableEquivalence_of_cone_stableGroup_subsingleton _
    (boundedFlatAffineSectionFullOpenBassTelescopeRestriction_coneFiber_isStableEquivalence j a)
    (boundedFlatAffineSectionFullOpenBassTelescopeRestriction_cone_stableGroup_subsingleton j a)

end Quillen.PerfectComplexes
