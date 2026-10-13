/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Basic
public import Mathlib.CategoryTheory.IsConnected

/-! # Connectedness of the Q-category

Every object receives a particular arrow from the vertex represented by zero.
This proves connectedness of the category, without claiming uniqueness of these
arrows or that the chosen vertex is an initial or zero object in Q.
-/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C)

/-- The distinguished object of Q, corresponding to zero in the original category. -/
abbrev qZero : E.QCategory := Quillen.Q.of E.deflation E.inflation (0 : C)

/-- The identity/zero admissible span supplies one arrow from the distinguished
vertex to any object. This does not assert that there is only one such arrow. -/
def fromZero (X : E.QCategory) : E.qZero ⟶ X :=
  Quillen.Q.mkHom E.deflation E.inflation
    { apex := 0
      l := 𝟙 _
      r := 0
      wl := E.deflation_id _
      wr := E.inflation_zero X.obj.of }

instance qCategory_nonempty : Nonempty E.QCategory := ⟨E.qZero⟩

/-- The Q-category is connected, by the zigzags X ← 0 → Y. -/
instance qCategory_isConnected : IsConnected E.QCategory := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α f hf X Y
  exact (hf (E.fromZero X)).symm.trans (hf (E.fromZero Y))

end Quillen.ExactStructure
