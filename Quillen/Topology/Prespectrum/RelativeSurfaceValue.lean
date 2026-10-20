/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopy

/-! Exact evaluation of a supplied relative prespectrum surface at both original times. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
/-- Evaluate the exact supplied whole relative surface. -/
def surfaceValue {E F : Quillen.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K : Quillen.LoopPrespectrum.Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) : F.space n :=
  J.level n (r, (s, x))
/-- The value is definitionally the supplied surface at both original times. -/
theorem surfaceValue_eq_level {E F : Quillen.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K : Quillen.LoopPrespectrum.Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    surfaceValue J n r s x = J.level n (r, (s, x)) := rfl
/-- A whole-level equality gives equality of the exact supplied surface values. -/
theorem surfaceValue_eq_of_level_eq {E F : Quillen.LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F}
    {H K : Quillen.LoopPrespectrum.Homotopy f g}
    {H' K' : Quillen.LoopPrespectrum.Homotopy f' g'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (n : ℕ)
    (e : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    surfaceValue J n r s x = surfaceValue J' n r s x :=
  DFunLike.congr_fun e _

/-- The first comparison face is the original first track. -/
theorem surfaceValue_zero {E F : Quillen.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K : Quillen.LoopPrespectrum.Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (s : unitInterval) (x : E.space n) :
    surfaceValue J n 0 s x = H.level n (s, x) :=
  (J.level n).apply_zero (s, x)

/-- The last comparison face is the original second track. -/
theorem surfaceValue_one {E F : Quillen.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K : Quillen.LoopPrespectrum.Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (s : unitInterval) (x : E.space n) :
    surfaceValue J n 1 s x = K.level n (s, x) :=
  (J.level n).apply_one (s, x)

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
