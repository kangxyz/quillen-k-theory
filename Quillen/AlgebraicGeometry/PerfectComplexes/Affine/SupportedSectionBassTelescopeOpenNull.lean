/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassOpenNullTransition
public import Quillen.Topology.Prespectrum.TelescopeConeDescent

/-!
# The original supported-to-relative-open Bass telescope null track

The actual finite-stage null tracks commute with the unchanged transitions. Their existing
quotient telescope homotopy therefore supplies the original support/open telescope null track.
Coefficient naturality is proved on every original cylinder, retaining its independent height
and null time. The endpoint is the same coarse relative-open telescope.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The literal telescope homotopy of the same original coefficient-natural finite null family. -/
def boundedFlatAffineSupportedSectionBassTelescopeOpenNull :
    DiagramNullHomotopy (boundedFlatAffineSupportedSectionBassTelescopeForget j)
      (boundedFlatAffineSectionBassTelescopeOpen j) where
  homotopy a := Telescope.mapNullHomotopy
    (fun n => (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
    (fun n => (boundedFlatAffineSupportedSectionBassTransition j n).app a)
    (fun n => (boundedFlatAffineSectionBassDiagram n).obj a.right)
    (fun n => (boundedFlatAffineSectionBassTransition n).app a.right)
    (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
    (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a)
    (fun n => (boundedFlatAffineSupportedSectionBassForget j n).app a)
    (fun n => (boundedFlatAffineSectionBassOpen j n).app a)
    (fun n => congrArg (fun f => f.app a)
      (boundedFlatAffineSupportedSectionBassForget_transition j n))
    (fun n => congrArg (fun f => f.app a)
      (boundedFlatAffineSectionBassOpen_transition j n))
    (fun n => (boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a)
    (fun n m r x => boundedFlatAffineSupportedSectionBassOpenNull_transition j n a m r x)
  naturality {a b} f m r x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj b)
          (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app b) m z.1
          (z.2.1, ((boundedFlatAffineSectionOpenBassDiagram j z.1).map f).map m
            (((boundedFlatAffineSupportedSectionBassOpenNull j z.1).homotopy a).level m
              (r, z.2.2))) =
        Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj b)
          (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app b) m z.1
          (z.2.1, ((boundedFlatAffineSupportedSectionBassOpenNull j z.1).homotopy b).level m
            (r, ((boundedFlatAffineSupportedSectionBassDiagram j z.1).map f).map m z.2.2))
      exact congrArg (fun y => Telescope.cylinder
        (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj b)
        (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app b) m z.1 (z.2.1, y))
        ((boundedFlatAffineSupportedSectionBassOpenNull j z.1).naturality f m r z.2.2)

/-- Every component is the specified original telescope null construction with the proved
whole finite-transition equation. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenNull_homotopy (a : Under R) :
    (boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a =
    Telescope.mapNullHomotopy
      (fun n => (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
      (fun n => (boundedFlatAffineSupportedSectionBassTransition j n).app a)
      (fun n => (boundedFlatAffineSectionBassDiagram n).obj a.right)
      (fun n => (boundedFlatAffineSectionBassTransition n).app a.right)
      (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
      (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a)
      (fun n => (boundedFlatAffineSupportedSectionBassForget j n).app a)
      (fun n => (boundedFlatAffineSectionBassOpen j n).app a)
      (fun n => congrArg (fun f => f.app a)
        (boundedFlatAffineSupportedSectionBassForget_transition j n))
      (fun n => congrArg (fun f => f.app a)
        (boundedFlatAffineSectionBassOpen_transition j n))
      (fun n => (boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a)
      (fun n m r x => boundedFlatAffineSupportedSectionBassOpenNull_transition j n a m r x) := rfl

/-- The original null time and telescope cylinder height are retained independently. -/
theorem boundedFlatAffineSupportedSectionBassTelescopeOpenNull_cylinder
    (a : Under R) (m i : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m
        (r, Telescope.cylinder
          (fun n => (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n => (boundedFlatAffineSupportedSectionBassTransition j n).app a) m i (t, x)) =
      Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a) m i
          (t, ((boundedFlatAffineSupportedSectionBassOpenNull j i).homotopy a).level m (r, x)) :=
  rfl

end Quillen.PerfectComplexes
