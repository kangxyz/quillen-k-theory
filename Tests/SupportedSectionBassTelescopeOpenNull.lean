/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassTelescopeOpenNull

/-!
# Consumers of the original whole support/open telescope null track

Every finite transition keeps the exact original null time, including degree zero. The
actual quotient telescope retains the independent null and cylinder coordinates, both
specified endpoint maps, and the unchanged coefficient maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.SupportedSectionBassTelescopeOpenNull
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual finite transition retains the specified null parameter at degree zero. -/
theorem originalDegreeZeroNullTransition (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j n).obj a).space 0) :
    ((boundedFlatAffineSectionOpenBassTransition j n).app a).map 0
        (((boundedFlatAffineSupportedSectionBassOpenNull j n).homotopy a).level 0 (r, x)) =
      ((boundedFlatAffineSupportedSectionBassOpenNull j (n + 1)).homotopy a).level 0
        (r, ((boundedFlatAffineSupportedSectionBassTransition j n).app a).map 0 x) :=
  boundedFlatAffineSupportedSectionBassOpenNull_transition j n a 0 r x

/-- The original telescope retains both the full null time and original cylinder height. -/
theorem originalTwoTimeCylinder (a : Under R) (m i : ℕ) (r t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassDiagram j i).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m
        (r, Telescope.cylinder
          (fun n => (boundedFlatAffineSupportedSectionBassDiagram j n).obj a)
          (fun n => (boundedFlatAffineSupportedSectionBassTransition j n).app a) m i (t, x)) =
      Telescope.cylinder (fun n => (boundedFlatAffineSectionOpenBassDiagram j n).obj a)
        (fun n => (boundedFlatAffineSectionOpenBassTransition j n).app a) m i
          (t, ((boundedFlatAffineSupportedSectionBassOpenNull j i).homotopy a).level m (r, x)) :=
  boundedFlatAffineSupportedSectionBassTelescopeOpenNull_cylinder j a m i r t x

/-- The initial null endpoint is the literal composite of the two original telescope maps. -/
theorem originalCompositeEndpoint (a : Under R) (m : ℕ)
    (x : ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m (0, x) =
      ((boundedFlatAffineSectionBassTelescopeOpen j).app a).map m
        (((boundedFlatAffineSupportedSectionBassTelescopeForget j).app a).map m x) :=
  ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).at_zero m x

/-- The original final null endpoint is the coarse telescope's actual chosen point. -/
theorem originalZeroEndpoint (a : Under R) (m : ℕ)
    (x : ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).space m) :
    ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m (1, x) =
      ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).obj a).point m :=
  ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).at_one m x

/-- Coefficient naturality preserves the entire original null path, at the same time. -/
theorem originalCoefficientTrack {a b : Under R} (f : a ⟶ b) (m : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).obj a).space m) :
    ((boundedFlatAffineSectionOpenBassTelescopeFunctor j).map f).map m
        (((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy a).level m (r, x)) =
      ((boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).homotopy b).level m
        (r, ((boundedFlatAffineSupportedSectionBassTelescopeFunctor j).map f).map m x) :=
  (boundedFlatAffineSupportedSectionBassTelescopeOpenNull j).naturality f m r x

end Quillen.Tests.SupportedSectionBassTelescopeOpenNull
