/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.CategoryTheory.TheoremB.NaturalTransformationFiberLift

/-! # Full source and path coordinates of the moving-source lift -/
noncomputable section
open CategoryTheory Quillen Quillen.TheoremB
universe u
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]

example {P Q : A ⥤ C} (τ : P ⟶ Q) (F : C ⥤ D) (d : D)
    (ε : Q ⋙ F ⟶ (Functor.const A).obj d) (t : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberHomotopy τ F d ε (t, x)).val.1 =
      classifyingSpaceNaturalTransformationHomotopy τ (t, x) := rfl

example {P Q : A ⥤ C} (τ : P ⟶ Q) (F : C ⥤ D) (d : D)
    (ε : Q ⋙ F ⟶ (Functor.const A).obj d) (s t : unitInterval)
    (x : ClassifyingSpace A) :
    (naturalTransformationFiberHomotopy τ F d ε (s, x)).val.2 t =
      functorChainBarycentric (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
        (x, sourceTriangleParameter s t) := rfl
