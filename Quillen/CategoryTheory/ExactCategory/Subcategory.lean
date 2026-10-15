/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Subcategory
public import Quillen.KTheory.Map.Basic

/-!
# K-maps of full exact subcategories

Aglib supplies the inherited exact structure and exact inclusion. This module
retains their Q-construction and K-group applications.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactSubcategory
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The Q-functor induced by the inherited exact inclusion. -/
def mapQ := (exactInclusion E P).mapQ

/-- The canonical homomorphism on genuine Quillen K-groups. -/
def KMap (n : ℕ) : (exactStructure E P).K n →* E.K n := (exactInclusion E P).KMap n

end CategoryTheory.ExactCategory.ExactSubcategory

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [E.IsExtensionClosed P] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- The canonical K-map from a full, replete, extension-closed subcategory
containing zero, with no ambient abelian hypothesis. -/
def fullSubcategoryKMap (n : ℕ) :
    letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
    (E.fullSubcategoryExactStructure P).K n →* E.K n := by
  letI : P.IsClosedUnderFiniteProducts := E.extensionClosed_finiteProducts P
  exact (E.fullSubcategoryExactInclusion P).KMap n

end CategoryTheory.ExactCategory.ExactStructure
