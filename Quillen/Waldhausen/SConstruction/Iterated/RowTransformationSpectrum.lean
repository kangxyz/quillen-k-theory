/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationRealization
public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopHomotopy

/-! # The whole spectrum cell of an independently realized first row

Positive levels retain the row and transformation times. Degree zero retains the additional
original input-loop coordinate. This does not assert a standard tensor-product qualification.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

/-- The original track with its actual first-row-compatible target. -/
def rowTransformationSpectrumHomotopy :
    LoopPrespectrum.Homotopy (prespectrumMap F ≫ rowStabilizationMap W)
      (prespectrumMap G ≫ rowStabilizationMap W) :=
  (prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)

/-- Positive levels agree with the independent double-cylinder realization. -/
theorem rowTransformationSpectrumHomotopy_succ (k : ℕ) (t s : unitInterval)
    (x : stageSpace k V) :
    Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level (k + 1) (t, x)) s =
      rowTransformationRealization η hη k (s, (t, x)) :=
  (rowTransformationRealization_structure η hη k s t x).symm

/-- Degree zero retains the source loop separately from both cell coordinates. -/
theorem rowTransformationSpectrumHomotopy_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap
      (Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level 0 (t, γ)) a) s =
      rowTransformationRealization η hη 0 (s, (t, γ a)) :=
  (rowTransformationRealization_structure η hη 0 s t (γ a)).symm

end Quillen.Waldhausen.IteratedS
