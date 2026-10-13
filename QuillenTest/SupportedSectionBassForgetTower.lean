/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassForgetTower

/-!
# Original supported Bass-tower inclusion consumers

These retain the original stage-zero inclusion, first cone map, actual seed iterates,
coefficient arrows, quotient cylinders and independent structure times. No equivalence
of support inclusion or negative localization endpoint is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace QuillenTest.SupportedSectionBassForgetTower

open Quillen
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The finite tower starts at the unchanged original support-forgetting map. -/
theorem original_stage_zero :
    boundedFlatAffineSupportedSectionBassForget j 0 =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j :=
  boundedFlatAffineSupportedSectionBassForget_zero j

/-- The first stage keeps the actual cone comparison under the original parameter looping. -/
theorem original_first_cone (a : Under R) :
    (boundedFlatAffineSupportedSectionBassForget j 1).app a =
      parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeForget j a) :=
  boundedFlatAffineSupportedSectionBassForget_one_app j a

/-- Every original iterated seed, including its ring restriction, commutes with inclusion. -/
theorem original_transition_square (n : ℕ) :
    boundedFlatAffineSupportedSectionBassForget j n ≫
        Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTransition n) =
      boundedFlatAffineSupportedSectionBassTransition j n ≫
        boundedFlatAffineSupportedSectionBassForget j (n + 1) :=
  boundedFlatAffineSupportedSectionBassForget_transition j n

/-- The actual quotient arrow retains the entire height of every original cylinder. -/
theorem original_telescope_cylinder (a : Under R) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    ((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map k
        (Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) k i (s, x)) =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
        (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right) k i
          (s, ((boundedFlatAffineSupportedSectionBassForget j i).app a).map k x) :=
  boundedFlatAffineSupportedSectionBassTelescopeForget_cylinder j a k i s x

/-- The actual stage faces commute at every finite index, not only at stage zero. -/
theorem original_stage_face (n : ℕ) :
    boundedFlatAffineSupportedSectionBassTelescopeInclusion j n ≫
        boundedFlatAffineSupportedSectionBassTelescopeForget j =
      boundedFlatAffineSupportedSectionBassForget j n ≫
        Functor.whiskerLeft (Under.forget R) (boundedFlatAffineSectionBassTelescopeInclusion n) :=
  boundedFlatAffineSupportedSectionBassTelescopeInclusion_forget j n

/-- The telescope triangle retains the original supported and ambient initial maps. -/
theorem original_initial_triangle :
    boundedFlatAffineSupportedSectionBassTelescopeInitial j ≫
        boundedFlatAffineSupportedSectionBassTelescopeForget j =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        Functor.whiskerLeft (Under.forget R) boundedFlatAffineSectionBassTelescopeInitial :=
  boundedFlatAffineSupportedSectionBassTelescopeInitial_forget j

/-- Naturality uses the unchanged coefficient map of the ambient original Bass telescope. -/
theorem original_coefficient_square {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f ≫
        (boundedFlatAffineSupportedSectionBassTelescopeForget j).app b =
      (boundedFlatAffineSupportedSectionBassTelescopeForget j).app a ≫
        boundedFlatAffineSectionBassTelescopeMap f.right :=
  (boundedFlatAffineSupportedSectionBassTelescopeForget j).naturality f

/-- The independent structure and cylinder times are retained in the actual target telescope. -/
theorem original_independent_times (a : Under R) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space k) :
    (boundedFlatAffineSectionBassTelescope a.right).structureMap k
        (((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map k
          (Telescope.cylinder (fun n ↦ (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
            (fun n ↦ (boundedFlatAffineSupportedSectionBassTransition j n).app a) k i (s, x))) t =
      Telescope.cylinder (fun n ↦ (boundedFlatAffineSectionBassDiagram n).obj a.right)
        (fun n ↦ (boundedFlatAffineSectionBassTransition n).app a.right) (k + 1) i
          (s, ((boundedFlatAffineSectionBassDiagram i).obj a.right).structureMap k
            (((boundedFlatAffineSupportedSectionBassForget j i).app a).map k x) t) := rfl

end QuillenTest.SupportedSectionBassForgetTower
