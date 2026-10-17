/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! Turn the actual equal-composite boundary comparison into a moving leg square. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedSpanCast
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.Homotopy
variable {E F : LoopPrespectrum.{u}}

/-- Precomposition of two original tracks ignores only their displayed endpoint casts. -/
theorem precomp_cast_pasting_level {D : LoopPrespectrum.{u}}
    {f₀ f₁ g₀ g₁ : E ⟶ F} (H : Homotopy f₀ f₁) (K : Homotopy g₀ g₁)
    (e : g₀ = f₀) (j : D ⟶ E) {a' b' m' : D ⟶ F}
    (ha : j ≫ f₁ = a') (hb : j ≫ g₁ = b') (hm : j ≫ f₀ = m') (n : ℕ) :
    ((Homotopy.precomp j (H.symm.trans (K.cast e rfl))).cast ha hb).level n =
      (((Homotopy.precomp j H).cast hm ha).symm.trans
        ((Homotopy.precomp j K).cast ((congrArg (fun f ↦ j ≫ f) e).trans hm) hb)).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  change ((H.symm.levelHomotopy n).trans ((K.cast e rfl).levelHomotopy n))
      (r, j.map n x) =
    ((((Homotopy.precomp j H).cast hm ha).symm.levelHomotopy n).trans
      (((Homotopy.precomp j K).cast ((congrArg (fun f ↦ j ≫ f) e).trans hm) hb).levelHomotopy n))
        (r, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

end Quillen.PerfectComplexes.CoefficientBassSeedSpanCast
