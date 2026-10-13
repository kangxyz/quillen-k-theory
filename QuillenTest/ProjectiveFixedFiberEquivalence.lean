/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveFixedFiberEquivalence
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Actual localized fixed-fiber equivalence consumers -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
open scoped MonoidalLeftAction
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction extensionIsoFiberDirectSumAction
attribute [local instance] extensionDeflationIsoFiberLinear

example (R : Type u) [Ring R] (C : Quillen.FiniteProjectiveModule.Category.{u, u} R)
    (A : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    (((localizedFixedExtensionFiberEquivalence R C).functor.obj ⟨(A, p)⟩).obj.right).obj =
      (A, (exactStructure R).extensionOfDeflation p.of) := rfl

example (R : Type u) [Ring R] (C : Quillen.FiniteProjectiveModule.Category.{u, u} R)
    (A : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    ((localizedFixedExtensionFiberEquivalence R C).functor.obj ⟨(A, p)⟩).obj.hom =
      ((exactStructure R).qIsoOfIso
        ((exactStructure R).extensionOfDeflationQuotientIso p.of)).inv := rfl

example (R : Type u) [Ring R] (C : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    LocalizedFixedExtensionCategory Rᵐᵒᵖ C ≌ IsoFiber (localizedExtensionProjection Rᵐᵒᵖ)
      (Q.of (exactStructure Rᵐᵒᵖ).deflation (exactStructure Rᵐᵒᵖ).inflation C) :=
  localizedFixedExtensionFiberEquivalence Rᵐᵒᵖ C

example (C : Quillen.FiniteProjectiveModule.Category (Matrix (Fin 2) (Fin 2) ℤ)) :
    ((localizedFixedExtensionFiberEquivalence
      (Matrix (Fin 2) (Fin 2) ℤ) C).functor).IsEquivalence :=
  inferInstance

example (C : Quillen.FiniteProjectiveModule.Category (ZMod 1)) :
    ((localizedFixedExtensionFiberEquivalence (ZMod 1) C).functor).IsEquivalence := inferInstance
