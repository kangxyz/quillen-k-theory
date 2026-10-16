/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryZero
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Cylinder.Subcategory
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout
public import Quillen.Waldhausen.ArrowCategory.Structure
public import Quillen.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # Actual middle-cylinder preservation in full complex subcategories

The original middle functor preserves zero objects and componentwise pushouts
along inherited admissible maps. It preserves both componentwise isomorphisms
and componentwise quasi-isomorphisms. All statements concern the unchanged
identity-cone cylinder and the actual full-subcategory maps.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v

namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- The actual middle cylinder preserves displayed pointwise pushouts along
inherited admissible maps, with no global ambient-pushout closure assumption. -/
theorem subcategoryMiddleFunctor_map_isPushout
    {K L M N : Arrow P.FullSubcategory} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hf : ArrowCategory.cof (complexSubcategory P) f)
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryMiddleFunctor P hcone).map f)
      ((subcategoryMiddleFunctor P hcone).map g)
      ((subcategoryMiddleFunctor P hcone).map i)
      ((subcategoryMiddleFunctor P hcone).map j) := by
  apply IsPushout.of_map_of_faithful P.ι
  exact middleFunctor_map_isPushout
    (fullSubcategory_map_pushout _ P hf.1 hL)
    (fullSubcategory_map_pushout _ P hf.2 hR)

/-- The target quasi-isomorphism alone suffices for the original middle map. -/
theorem subcategoryMiddleFunctor_map_weak {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (complexSubcategory P).weq α.right) :
    (complexSubcategory P).weq ((subcategoryMiddleFunctor P hcone).map α) := by
  let : QuasiIso (P.ι.mapArrow.map α).right := hα
  exact middleFunctor_map_quasiIso (P.ι.mapArrow.map α)

end Quillen.Waldhausen.SplitFactorization
