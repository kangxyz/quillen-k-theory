/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIdentityAction

/-!
# Original target-action consumers

The actual Model arrow is retained at degree zero, with its independent loop coordinate.
Its original structure parameter also commutes with the same whole whiskered target action.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.PrespectrumIdentityAction
variable {V W : Model.{u}} (F : V ⟶ W) (e : 𝟭 W ≅ 𝟭 W)

/-- Original degree-zero loop values retain the actual Model map and both independent times. -/
theorem original_zero_level (s t : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap
        ((prespectrumIsoHomotopy F
          (Quillen.FunctorIdentityAutomorphism.onFunctor F.functor e)).level 0 (s, γ)) t =
      Path.toContinuousMap ((prespectrumIsoHomotopy (𝟙 W) e).level 0
        (s, (prespectrumMap F).map 0 γ)) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (prespectrumIsoHomotopy_onFunctor_apply F e 0 s γ)

/-- The exact same target action retains the original structure time. -/
theorem original_structure_time (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumIsoHomotopy F
        (Quillen.FunctorIdentityAutomorphism.onFunctor F.functor e)).level (n + 1)
        (s, (prespectrum V).structureMap n x t) =
      (prespectrum W).structureMap n
        ((prespectrumIsoHomotopy (𝟙 W) e).level n (s, (prespectrumMap F).map n x)) t := by
  rw [(prespectrumIsoHomotopy F
      (Quillen.FunctorIdentityAutomorphism.onFunctor F.functor e)).comm]
  rw [prespectrumIsoHomotopy_onFunctor_apply]

end Quillen.Tests.PrespectrumIdentityAction
