/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.CategoryTheory.ExactCategory.ExtensionTotal

open CategoryTheory.ExactCategory


/-! # Subdivision orientation and actual quotient presentations -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe u v
variable {C : Type u} [Category.{v} C]

example {A B A' B' : C} {i : A ⟶ B} {j : A' ⟶ B'}
    (h : A' ⟶ A) (k : B ⟶ B') (w : h ≫ i ≫ k = j) :
    Subdivision.of i ⟶ Subdivision.of j := Subdivision.mkHom h k w

example {X Y : Subdivision C} (f : X ⟶ Y) :
    Subdivision.domainMap f ≫ X.fiber.unop.hom ≫ f.base = Y.fiber.unop.hom :=
  Subdivision.factorization f

variable [Preadditive C] [HasFiniteBiproducts C] (E : ExactStructure C)

example {A B : C} (i : A ⟶ B) (hi : E.inflation i) : E.ExtensionTotal :=
  E.extensionTotalOf i hi

example (x : E.ExtensionTotal) :
    IsColimit (CokernelCofork.ofπ (E.extensionQuotientData x).π
      (E.extensionQuotientData x).zero) := (E.extensionQuotientData x).isColimit E

example {x : E.ExtensionTotal} (q r : E.ExtensionQuotientData x) :
    q.π ≫ (q.iso E r).hom = r.π := q.π_iso_hom E r
