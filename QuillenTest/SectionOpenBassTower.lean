/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassOpenTower

/-!
# Consumers of the original relative-open Bass tower

The initial transition retains the actual Laurent seed. The existing ambient ring tower maps
into the original relative-open tower at every stage and cylinder height, including the exact
stage-zero section map. Arbitrary coefficient arrows and structure times remain visible.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionOpenBassTower

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The first original coarse transition retains the original Laurent seed and output time. -/
theorem originalInitialSeed (a : Under R) (m : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space m) :
    Path.toContinuousMap
        (((boundedFlatAffineSectionOpenBassTransition j 0).app a).map m x) t =
      Path.toContinuousMap ((boundedFlatAffineSectionOpenBassSeedMap j a).map m x) t := rfl

/-- The original ambient and coarse successors agree on every degree-zero point. -/
theorem originalDegreeZeroTransition (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSectionBassDiagram n).obj a.right).space 0) :
    ((boundedFlatAffineSectionOpenBassTransition j n).app a).map 0
        (((boundedFlatAffineSectionBassOpen j n).app a).map 0 x) =
      ((boundedFlatAffineSectionBassOpen j (n + 1)).app a).map 0
        (((boundedFlatAffineSectionBassTransition n).app a.right).map 0 x) :=
  congrArg (fun f => (f.app a).map 0 x)
    (boundedFlatAffineSectionBassOpen_transition j n)

/-- The original ambient stage point enters the same coarse cylinder at the same height. -/
theorem originalAmbientCylinder (a : Under R) (m i : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj a.right).space m) :
    ((boundedFlatAffineSectionBassTelescopeOpen j).app a).map m
        (Telescope.cylinder (fun n => (boundedFlatAffineSectionBassDiagram n).obj a.right)
          (fun n => (boundedFlatAffineSectionBassTransition n).app a.right) m i (t, x)) =
      Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a) m i
          (t, ((boundedFlatAffineSectionBassOpen j i).app a).map m x) :=
  boundedFlatAffineSectionBassTelescopeOpen_cylinder j a m i t x

/-- Every original coefficient arrow acts on the actual coarse cylinder without changing height. -/
theorem originalCoefficientCylinder {a b : Under R} (f : a ⟶ b)
    (m i : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).map f).map m
        (Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
          (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a) m i (t, x)) =
      Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj b)
        (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app b) m i
          (t, ((boundedFlatAffineSectionOpenBassDiagram j i).map f).map m x) :=
  boundedFlatAffineSectionOpenBassTelescopeFunctor_map_cylinder j f m i t x

/-- The same original fine-to-coarse map occurs on the initial section face. -/
theorem originalInitialSectionMap :
    Functor.whiskerLeft (Under.forget R) boundedFlatAffineSectionBassTelescopeInitial ≫
        boundedFlatAffineSectionBassTelescopeOpen j =
      boundedFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedFlatAffineSectionOpenBassTelescopeInitial j :=
  boundedFlatAffineSectionBassTelescopeInitial_open j

/-- The actual ambient-to-coarse telescope map retains every original structure coordinate. -/
theorem originalStructureTime (a : Under R) (m : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionBassTelescope a.right).space m) :
    ((boundedFlatAffineSectionBassTelescopeOpen j).app a).map (m + 1)
        ((boundedFlatAffineSectionBassTelescope a.right).structureMap m x t) =
      ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).obj a).structureMap m
        (((boundedFlatAffineSectionBassTelescopeOpen j).app a).map m x) t :=
  congrArg (fun γ => γ t) (((boundedFlatAffineSectionBassTelescopeOpen j).app a).comm m x)

end QuillenTest.SectionOpenBassTower
