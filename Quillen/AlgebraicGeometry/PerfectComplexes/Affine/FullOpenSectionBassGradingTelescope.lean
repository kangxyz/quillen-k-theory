/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassGradingTower
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap

/-!
# The original grading arrow on the actual fine full-open Bass telescope

The unchanged finite grading maps induce the coefficient-natural reduced telescope arrow.
It retains every original stage inclusion and full cylinder height. Its target is the actual
quotient-graded telescope whose signed stable groups already vanish. Consequently the grading
arrow induces zero on signed stable groups; no vanishing of its fine source is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

variable [CompactSpace U]

/-- The actual telescope grading map is induced by the original finite grading maps. -/
def boundedFlatAffineFullOpenSectionBassTelescopeGrading :
    boundedFlatAffineFullOpenSectionBassTelescopeFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j :=
  Telescope.diagramMap (boundedFlatAffineFullOpenSectionBassDiagram j)
    (boundedFlatAffineFullOpenGradedSectionBassDiagram j)
    (boundedFlatAffineFullOpenSectionBassTransition j)
    (boundedFlatAffineFullOpenGradedSectionBassTransition j)
    (boundedFlatAffineFullOpenSectionBassGrading j)
    (boundedFlatAffineFullOpenSectionBassGrading_transition j)

/-- Every level, finite stage and whole cylinder height is unchanged by grading. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeGrading_cylinder
    (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionBassDiagram j i).obj a).space n) :
    ((boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app a).map n
        (Telescope.cylinder
          (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj a)
          (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app a) n i (s, x)) =
      Telescope.cylinder
        (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassDiagram j k).obj a)
        (fun k ↦ (boundedFlatAffineFullOpenGradedSectionBassTransition j k).app a) n i
        (s, ((boundedFlatAffineFullOpenSectionBassGrading j i).app a).map n x) := rfl

/-- The original grading arrow commutes literally with every actual stage inclusion. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeInclusion_grading (i : ℕ) :
    boundedFlatAffineFullOpenSectionBassTelescopeInclusion j i ≫
        boundedFlatAffineFullOpenSectionBassTelescopeGrading j =
      boundedFlatAffineFullOpenSectionBassGrading j i ≫
        boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion j i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The stage-zero face is the original fine-to-graded section transformation. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeInitial_grading :
    boundedFlatAffineFullOpenSectionBassTelescopeInitial j ≫
        boundedFlatAffineFullOpenSectionBassTelescopeGrading j =
      boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j ≫
        boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion j 0 :=
  boundedFlatAffineFullOpenSectionBassTelescopeInclusion_grading j 0

/-- The complete actual telescope grading arrow is strictly natural in every coefficient map. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeGrading_naturality
    {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).map f ≫
        (boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app b =
      (boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app a ≫
        (boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j).map f :=
  (boundedFlatAffineFullOpenSectionBassTelescopeGrading j).naturality f

/-- Every signed stable class maps to zero in the actual quotient-graded telescope. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeGrading_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      ((boundedFlatAffineFullOpenSectionBassTelescopeFunctor j).obj a) d) :
    (stableHomotopyFunctor d).map
      ((boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app a) x = 0 :=
  boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d _

/-- The grading telescope arrow induces the zero map in every original signed stable degree. -/
theorem boundedFlatAffineFullOpenSectionBassTelescopeGrading_stableMap_eq_zero
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatAffineFullOpenSectionBassTelescopeGrading j).app a) = 0 := by
  apply AddCommGrpCat.ext
  intro x
  exact boundedFlatAffineFullOpenSectionBassTelescopeGrading_stableClass_eq_zero j a d x

end Quillen.PerfectComplexes
