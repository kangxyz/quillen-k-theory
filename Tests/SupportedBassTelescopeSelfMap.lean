/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeSelfMap

/-!
# Actual supported telescope self-map consumers

The identity algebra still uses the specified pullback of the original open. The original
supported seed, each finite transition, the whole cylinder and loop parameters, actual Under
coefficient maps and all negative signed degrees are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SupportedBassTelescopeSelfMap
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The honest identity-algebra pullback enters at original level zero through its same seed. -/
theorem original_identity_pullback_initial
    (x : (Waldhausen.IteratedS.prespectrum (boundedFlatAffineSupportedSectionModel
      (Scheme.AffineOpenPair.inclusion j (Under.mk (𝟙 R))))).space 0) :
    ((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app (Under.mk (𝟙 R))).map 0
        (((boundedFlatAffineSupportedSectionBassTelescopeInitial j).app
          (Under.mk (𝟙 R))).map 0 x) =
      (((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSupportedSectionBassTelescopeInitial j)).app
          (Under.mk (𝟙 R))).map 0
        (((boundedFlatAffineSupportedSectionBassSeed j).app (Under.mk (𝟙 R))).map 0 x) :=
  congrArg (fun m => m.map 0 x)
    (boundedFlatAffineSupportedSectionBassTelescopeBassMap_initial j (Under.mk (𝟙 R)))

/-- The actual Under coefficient map retains the entire cylinder and independent loop time. -/
theorem original_coefficient_cylinder_loop {a b : Under R} (f : a ⟶ b)
    (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    Path.toContinuousMap
        ((((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
            (boundedFlatAffineSupportedSectionBassTelescopeFunctor j)).map f).map k
          (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k
            (Telescope.cylinder
              (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
              (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a)
              k i (s, x)))) t =
      Path.toContinuousMap
        (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app b).map k
          (Telescope.cylinder
            (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj b)
            (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app b) k i
            (s, ((boundedFlatAffineSupportedSectionBassDiagram j i).map f).map k x))) t :=
  (congrArg (fun m => Path.toContinuousMap (m.map k
      (Telescope.cylinder (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
        (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k i (s, x))) t)
    ((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).naturality f)).symm

/-- Height one is glued through the unchanged actual supported stage transition. -/
theorem original_seed_gluing (a : Under R) (k i : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    Path.toContinuousMap
        (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k
          (Telescope.cylinder
            (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
            (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k i (1, x))) t =
      Path.toContinuousMap
        (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k
          (Telescope.cylinder
            (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
            (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k (i + 1)
            (0, ((boundedFlatAffineSupportedSectionBassTransition j i).app a).map k x))) t :=
  congrArg (fun y => Path.toContinuousMap
    (((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a).map k y) t)
    (Telescope.cylinder_one
      (fun i => (boundedFlatAffineSupportedSectionBassDiagram j i).obj a)
      (fun i => (boundedFlatAffineSupportedSectionBassTransition j i).app a) k i x)

/-- Every negative original signed group sees a bijection, with no finite-stage premise. -/
theorem original_negative_bijective (a : Under R) (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((n + 1 : ℕ) : ℤ))).map
      ((boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a)) := by
  let := boundedFlatAffineSupportedSectionBassTelescopeBassMap_isStableEquivalence j a
    (-((n + 1 : ℕ) : ℤ))
  exact ConcreteCategory.bijective_of_isIso _

/-- Two original coefficient arrows commute with the same supported self-map. -/
theorem original_under_composition {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    (boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f ≫
        (boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map g ≫
        (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app c =
      (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).app a ≫
        ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatAffineSupportedSectionBassTelescopeFunctor j)).map (f ≫ g) := by
  simpa only [Functor.map_comp, Category.assoc] using
    (boundedFlatAffineSupportedSectionBassTelescopeBassMap j).naturality (f ≫ g)

end Quillen.Tests.SupportedBassTelescopeSelfMap
