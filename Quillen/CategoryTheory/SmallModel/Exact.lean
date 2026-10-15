/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Exact
public import Quillen.KTheory.Equivalence

/-!
# K-theory of exact small models

The general exact small models and presentation comparisons come from Aglib.
This module supplies their Q-construction and K-group applications.
-/
@[expose] public section

noncomputable section
universe w v v' u u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [EssentiallySmall.{w} C] (E : ExactStructure C)

instance smallModelToOriginal_mapQ_isEquivalence : E.smallModelToOriginal.mapQ.IsEquivalence :=
  E.smallModelToOriginal.mapQ_isEquivalence_of_equivalence
    (fun i => (E.ofEquivalence_inflation_iff (equivSmallModel.{w} C).symm i).2)
    (fun p => (E.ofEquivalence_deflation_iff (equivSmallModel.{w} C).symm p).2)

/-- K-theory formed from an actual `w`-small exact model. -/
abbrev SmallK (n : ℕ) := E.smallModel.K n

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The canonical homomorphism of small-model K-groups. -/
def smallKMap (F : ExactFunctor EC ED) (n : ℕ) : EC.SmallK n →* ED.SmallK n :=
  F.smallModel.KMap n
end CategoryTheory.ExactCategory.ExactFunctor

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)
  {S T : Type w} [Category.{w} S] [Category.{w} T]
  [Preadditive S] [Preadditive T] [HasFiniteBiproducts S] [HasFiniteBiproducts T]
  (e : S ≌ C) (f : T ≌ C) [e.functor.Additive] [f.functor.Additive]

instance presentationComparison_mapQ_isEquivalence :
    (E.presentationComparison e f).mapQ.IsEquivalence :=
  (E.presentationComparison e f).mapQ_isEquivalence_of_equivalence
    (fun i => (E.presentationComparison_map_inflation_iff e f i).1)
    (fun p => (E.presentationComparison_map_deflation_iff e f p).1)

/-- Independence of the small exact presentation, as an actual equivalence of
K-groups whose forward map comes from the exact comparison functor. -/
def presentationKEquiv (n : ℕ) : (E.ofEquivalence e).K n ≃* (E.ofEquivalence f).K n :=
  (E.presentationComparison e f).KEquivOfMapQIsEquivalence n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma presentationKEquiv_coe (n : ℕ) :
    ↑(E.presentationKEquiv e f n) = (E.presentationComparison e f).KMap n := rfl
end CategoryTheory.ExactCategory.ExactStructure
