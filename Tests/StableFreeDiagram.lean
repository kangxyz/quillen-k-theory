/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.StableFreeDiagram

/-! Regression tests for original finite-stage arrows in the projective telescope comparison. -/

open CategoryTheory Quillen Quillen.FiniteProjectiveModule.StableFree

universe u
variable {R : Type u} [Ring R]

example {n m : ℕ} (h : n ≤ m) (g : StableGeneralLinear.GL R n) :
    ((powerGroupDiagram R).map (homOfLE h)).hom (powerEndEquiv R n g) =
      powerEndEquiv R m (StableGeneralLinear.transition R n m h g) := by
  have hn := (matrixToPowerDiagram R).naturality (homOfLE h)
  exact (congrArg (fun f => f.hom g) hn).symm

example (n : ℕ) :
    (matrixPowerDiagramIso R).hom.app n ≫ (matrixPowerDiagramIso R).inv.app n =
      𝟙 ((matrixGroupDiagram R).obj n) := by
  exact NatTrans.congr_app (matrixPowerDiagramIso R).hom_inv_id n
