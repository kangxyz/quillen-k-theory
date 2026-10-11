/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeSelfMapForget

/-!
# Original support-forgetting self-map square consumers

The four actual maps, unchanged finite support inclusions, every cylinder and loop parameter,
original initial supported face, all signed groups and honest Under coefficient maps are kept.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SupportedBassTelescopeSelfMapForget
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Both whole parameters commute through the unchanged finite support-forgetting map. -/
theorem original_forgetting_cylinder_loop (a : Under R) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    Path.toContinuousMap
        ((((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
            (boundedFlatAffineSupportedSectionBassTelescopeForget j)).app a).map k
          (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k
            (Telescope.cylinder
              (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
              (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a)
              k i (s, x)))) t =
      Path.toContinuousMap
        ((boundedFlatAffineSectionBassTelescopeBassMap.app a.right).map k
          (Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram i).obj a.right)
            (fun i => (boundedFlatAffineSectionBassTransition i).app a.right) k i
            (s, ((boundedFlatAffineSupportedSectionBassForget j i).app a).map k x))) t :=
  congrArg (fun m => Path.toContinuousMap (m.map k
    (Telescope.cylinder (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
      (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k i (s, x))) t)
    (boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget_app j a)

/-- The original initial support map is retained by the entire self-comparison square. -/
theorem original_initial_forgetting :
    boundedFlatAffineSupportedSectionBassTelescopeInitial j ≫
        boundedFlatAffineSupportedSectionBassTelescopeBassMap j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeForget j) =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        Functor.whiskerLeft (Under.forget R) boundedFlatAffineSectionBassTelescopeInitial ≫
        KTheory.Bass.strictRingDiagramUnderSeed R boundedFlatAffineSectionBassTelescopeBassMap := by
  rw [boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget,
    ← Category.assoc, boundedFlatAffineSupportedSectionBassTelescopeInitial_forget,
    Category.assoc]

/-- Every signed degree keeps the original four stable maps in the exact commuting square. -/
theorem original_signed_forgetting (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
        ((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a) ≫
        (stableHomotopyFunctor d).map
          (((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
            (boundedFlatAffineSupportedSectionBassTelescopeForget j)).app a) =
      (stableHomotopyFunctor d).map
          ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a) ≫
        (stableHomotopyFunctor d).map
          (boundedFlatAffineSectionBassTelescopeBassMap.app a.right) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget_app]

/-- The original Under arrow becomes its unchanged ambient ring arrow in the whole square. -/
theorem original_under_forgetting {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f ≫
        (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app b ≫
        ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionBassTelescopeForget j)).app b =
      (boundedFlatAffineSupportedSectionBassTelescopeForget j).app a ≫
        boundedFlatAffineSectionBassTelescopeFunctor.map f.right ≫
        boundedFlatAffineSectionBassTelescopeBassMap.app b.right := by
  rw [boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget_app, ← Category.assoc,
    (boundedFlatAffineSupportedSectionBassTelescopeForget j).naturality f, Category.assoc]
  rfl

end Quillen.Tests.SupportedBassTelescopeSelfMapForget
