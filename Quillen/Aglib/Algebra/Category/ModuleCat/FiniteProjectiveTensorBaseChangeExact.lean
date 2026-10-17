/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor

/-!
# Exactness of literal tensor extension on finite projectives

Every conflation of finite projective modules splits. Applying the additive
literal tensor functor to that splitting proves exactness for every ring map,
without a flatness assumption and without changing its quotient carrier.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

universe u v

namespace Quillen.FiniteProjectiveModule

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The literal balanced tensor functor preserves the inherited exact structures. -/
def rightTensorBaseChangeExact (f : R →+* S) :
    ExactFunctor (exactStructure.{u, u} Rᵐᵒᵖ) (exactStructure.{v, max u v} Sᵐᵒᵖ) where
  toFunctor := rightTensorBaseChange f
  map_conflation K hK :=
    (conflation_iff_nonempty_splitting Sᵐᵒᵖ (K.map (rightTensorBaseChange f))).mpr
      ⟨(splittingOfConflation Rᵐᵒᵖ K hK).map (rightTensorBaseChange f)⟩

end Quillen.FiniteProjectiveModule
