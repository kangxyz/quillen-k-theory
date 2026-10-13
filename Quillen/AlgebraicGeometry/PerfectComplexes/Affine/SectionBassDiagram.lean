/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.KTheory.Bass.StrictRingDiagram

/-!
# Actual iterated Bass diagrams of the geometric section prespectrum

The genuine strict section prespectrum now instantiates the polynomial/Laurent Bass endofunctor.
Every iterate is an actual strict ring diagram with all coefficient maps. Connecting arrows
still require a proved strict geometric seed; no seed is assumed or introduced here.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Apply the actual Bass endofunctor repeatedly to the genuine geometric section diagram. -/
def boundedFlatAffineSectionBassDiagram (n : ℕ) : CommRingCat.{u} ⥤ LoopPrespectrum.{u+1} :=
  (KTheory.Bass.strictRingDiagramIterate n).obj boundedFlatAffineSectionPrespectrumFunctor

/-- The initial stage is the original strict section prespectrum diagram. -/
theorem boundedFlatAffineSectionBassDiagram_zero :
    boundedFlatAffineSectionBassDiagram.{u} 0 =
      boundedFlatAffineSectionPrespectrumFunctor := rfl

/-- Successor iteration applies the same Bass functor to the same original diagram. -/
theorem boundedFlatAffineSectionBassDiagram_succ (n : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} (n+1) =
      (KTheory.Bass.strictRingDiagramIterate n).obj
        (KTheory.Bass.strictRingDiagramFunctor.obj
          boundedFlatAffineSectionPrespectrumFunctor) := rfl

end Quillen.PerfectComplexes
