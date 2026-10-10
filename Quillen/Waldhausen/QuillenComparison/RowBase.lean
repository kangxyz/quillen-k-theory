/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.FlagPresentation
public import Quillen.Waldhausen.QuillenComparison.FlagExtension
public import Quillen.Waldhausen.QuillenComparison.RowFull

/-! # The zero-length Q-chain is realized by an actual exact row -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- The admissible one-step flag zero to the specified object. -/
def objectFlag (X : C) : ComposableArrows C 1 := zeroPrefixFlag (mk₀ X)

theorem objectFlag_inflation (X : C) {i j : Fin 2} (f : i ⟶ j) :
    E.inflation ((objectFlag X).map f) :=
  zeroPrefixFlag_inflation E (mk₀ X) (fun _ ↦ E.inflation_id X) f

/-- The one-step exact row representing a zero-length Q-chain. -/
def objectRow (X : C) : Row E (Edgewise.ε.obj ⦋0⦌) :=
  flagRow E (objectFlag X) (objectFlag_inflation E X)

/-- Its central quotient is canonically the specified object. -/
def objectRowCentralIso (X : C) :
    (objectRow E X).diagram.obj (nestedToInterval (centralInterval ⦋0⦌ 0)) ≅ X :=
  ((initialCompletionIso E (objectFlag X) (objectFlag_inflation E X)
    (Limits.isZero_zero C)).app (Fin.last 1)).symm

/-- Every zero-length Q-chain has an actual row preimage up to isomorphism. -/
def objectRowChainIso (G : ComposableArrows (Q E.deflation E.inflation) 0) :
    ((rowChainComparison E ⦋0⦌).obj (objectRow E (G.obj 0).obj.of)).of ≅ G :=
  ComposableArrows.isoMk₀ (E.qIsoOfIso (objectRowCentralIso E (G.obj 0).obj.of))

end Quillen.Waldhausen.QuillenComparison
