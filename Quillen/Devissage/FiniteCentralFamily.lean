/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Devissage.CentralEndomorphism
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.FiniteCentralFamily

/-!
# Dévissage for a finite family of locally nilpotent central operators

The filtration is built from actual images of the operators and refined by
pullback splicing. No bound uniform in the object is required.
-/
@[expose] public section

open Quillen.PrincipalSupportDevissage


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteCentralDevissage
open PrincipalSupportDevissage
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical inclusion of jointly annihilated objects induces the
actual homotopical dévissage isomorphism in every degree. -/
def KEquiv {C : Type u} [Category.{u} C] [Abelian C]
    (ts : List (𝟭 C ⟶ 𝟭 C))
    (h : ∀ X : C, ∀ t ∈ ts, ∃ n : ℕ, power t X n = 0) (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (killedByAll ts)).K n ≃*
      (abelianExactStructure C).K n :=
  Devissage.KEquiv _ (filtrationHypothesis ts h) n

end Quillen.FiniteCentralDevissage
