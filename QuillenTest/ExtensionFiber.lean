/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.CategoryTheory.ExactCategory.ExtensionFiber
import Quillen.Algebra.Category.ModuleCat.FiniteProjective

open CategoryTheory.ExactCategory


/-! # Extension fibers and their actual kernel presentations -/

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open Quillen

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example : E.ExtensionFiber (0 : C) ≌ Core C := E.extensionFiberZeroEquivalence

example {X : C} (p : E.ExtensionOver X) :
    IsLimit (KernelFork.ofι (E.extensionKernelData p).ι (E.extensionKernelData p).zero) :=
  (E.extensionKernelData p).isLimit E

example {X : C} (p : E.ExtensionOver X) (k l : E.ExtensionKernelData p) :
    (k.iso E l).hom ≫ l.ι = k.ι := k.iso_hom_ι E l

example {X Y : C} (f : X ⟶ Y) (hf : E.deflation f) :
    E.ExtensionFiber X ⥤ E.ExtensionFiber Y := E.extensionFiberPostcompose f hf

example (R : Type u) [Ring R] :
    (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).ExtensionFiber (0 :
      FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) ≌
        Core (FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :=
  (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).extensionFiberZeroEquivalence
