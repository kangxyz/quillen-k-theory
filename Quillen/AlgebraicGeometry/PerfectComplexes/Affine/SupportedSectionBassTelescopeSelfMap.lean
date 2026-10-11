/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTower
public import Quillen.KTheory.Bass.StrictDiagramSelfMap
public import Quillen.KTheory.Bass.ModelDiagramConnectivity

/-!
# The actual supported Bass telescope maps stably to its Bass image

The fixed-open Under-R diagram retains its actual pulled-back open at every coefficient.
The single original supported Laurent seed gives the map. Original iterated-S separation and
actual Bass closure discharge all topology assumptions, without finite-stage stabilization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Every actual supported Bass stage is T1 at every original level and coefficient object. -/
instance boundedFlatAffineSupportedSectionBassDiagramSpaceT1Space
    (i : ℕ) (a : Under R) (k : ℕ) :
    T1Space (((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :=
  KTheory.Bass.modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
    (boundedFlatAffineSupportedSectionModelFunctor j) a k

/-- The original supported telescope maps to its actual Under-R Bass image. -/
def boundedFlatAffineSupportedSectionBassTelescopeBassMap :
    boundedFlatAffineSupportedSectionBassTelescopeFunctor j ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatAffineSupportedSectionBassTelescopeFunctor j) :=
  KTheory.Bass.strictDiagramTelescopeSelfMap (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionBassSeed j)

/-- The exact original supported map is stable at every coefficient, in every signed degree. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a) := by
  let : ∀ i a k, T1Space
      ((((KTheory.Bass.strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
        (boundedFlatAffineSupportedSectionPrespectrumFunctor j)).obj a).space k) :=
    fun i a k => boundedFlatAffineSupportedSectionBassDiagramSpaceT1Space j i a k
  exact KTheory.Bass.strictDiagramTelescopeSelfMap_isStableEquivalence
    (laurentUnderSquareFunctor R) (boundedFlatAffineSupportedSectionBassSeed j) a

/-- Each unchanged supported stage face retains its actual iterated seed and successor cast. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_inclusion
    (i : ℕ) (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeInclusion j i).app a ≫
        (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a =
      (boundedFlatAffineSupportedSectionBassTransition j i).app a ≫
        (KTheory.Bass.strictDiagramSuccessorMap (laurentUnderSquareFunctor R)
          (boundedFlatAffineSupportedSectionPrespectrumFunctor j) i).app a ≫
        ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeInclusion j i)).app a := by
  exact (KTheory.Bass.strictDiagramTelescopeSelfMap_inclusion
    (laurentUnderSquareFunctor R) (boundedFlatAffineSupportedSectionBassSeed j) i a).trans
      (Category.assoc _ _ _)

/-- The actual initial supported face retains exactly the original supported Laurent seed. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_initial (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeInitial j).app a ≫
        (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a =
      (boundedFlatAffineSupportedSectionBassSeed j).app a ≫
        ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeInitial j)).app a :=
  KTheory.Bass.strictDiagramTelescopeSelfMap_initial (laurentUnderSquareFunctor R)
    (boundedFlatAffineSupportedSectionBassSeed j) a

/-- The entire original supported cylinder and independent loop coordinate remain literal. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeBassMap_cylinder
    (a : Under R) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    Path.toContinuousMap
        (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k
          (Telescope.cylinder
            (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
            (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k i (s, x))) t =
      (Telescope.diagramConeIso (boundedFlatAffineSupportedSectionBassDiagram j)
        (boundedFlatAffineSupportedSectionBassTransition j)
        ((laurentUnderSquareFunctor R).obj a)).inv.map k
        (Telescope.cylinder
          (fun i => mappingCone (StrictSquare.comparison
            ((boundedFlatAffineSupportedSectionBassDiagram j i).mapArrow.mapArrow.obj
              ((laurentUnderSquareFunctor R).obj a))))
          (Telescope.diagramConeTransition (boundedFlatAffineSupportedSectionBassDiagram j)
            (boundedFlatAffineSupportedSectionBassTransition j)
            ((laurentUnderSquareFunctor R).obj a)) k i
          (s, Path.toContinuousMap
            (((KTheory.Bass.strictDiagramSuccessorMap (laurentUnderSquareFunctor R)
                (boundedFlatAffineSupportedSectionPrespectrumFunctor j) i).app a).map k
              (((boundedFlatAffineSupportedSectionBassTransition j i).app a).map k x)) t)) := rfl

end Quillen.PerfectComplexes
