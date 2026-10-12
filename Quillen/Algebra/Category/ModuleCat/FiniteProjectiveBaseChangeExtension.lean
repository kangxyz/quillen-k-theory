/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeMonoidal
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveInflationAction
public import Quillen.CategoryTheory.ExactCategory.ExtensionFunctorProjection
public import Quillen.CategoryTheory.GroupCompletion.ActorChange

/-! # The original direct-sum comparison on base-changed extensions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The existing exact base-change functor on the actual extension category. -/
abbrev rightBaseChangeExtension := (rightBaseChangeExact f).extensionTotalFunctor

/-- The original coproduct comparison viewed as an admissible-inflation isomorphism. -/
def rightBaseChangeInflationTensorIso (P : IsoCategory Rᵐᵒᵖ)
    (X : (exactStructure Rᵐᵒᵖ).InflationCategory) :
    (rightBaseChangeCore f).obj P ⊙ₗ (rightBaseChangeExact f).inflationFunctor.obj X ≅
      (rightBaseChangeExact f).inflationFunctor.obj (P ⊙ₗ X) :=
  WideSubcategory.isoMk (rightBaseChangeTensorIso f P.of X.obj)
    ((exactStructure Sᵐᵒᵖ).inflation_of_iso (rightBaseChangeTensorIso f P.of X.obj))
    ((exactStructure Sᵐᵒᵖ).inflation_of_iso (rightBaseChangeTensorIso f P.of X.obj).symm)

/-- The real extension lineator reverses the kernel comparison and preserves the middle one. -/
def rightBaseChangeExtensionTensorIso (P : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (rightBaseChangeCore f).obj P ⊙ₗ (rightBaseChangeExtension f).obj x ≅
      (rightBaseChangeExtension f).obj (P ⊙ₗ x) :=
  Subdivision.isoMk
    (rightBaseChangeInflationTensorIso f P x.fiber.unop.left)
    (rightBaseChangeInflationTensorIso f P x.base) (by
      apply WideSubcategory.hom_ext
      exact Functor.LaxMonoidal.μ_natural_right (rightBaseChange f) P.of
        x.fiber.unop.hom.hom)

/-- The reversed kernel map is literally the inverse original tensor comparison. -/
theorem rightBaseChangeExtensionTensorIso_domain (P : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (Subdivision.domainMap (rightBaseChangeExtensionTensorIso f P x).hom).hom =
      (rightBaseChangeTensorIso f P.of x.fiber.unop.left.obj).inv := rfl

/-- The middle-object map is literally the forward original tensor comparison. -/
theorem rightBaseChangeExtensionTensorIso_middle (P : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (rightBaseChangeExtensionTensorIso f P x).hom.base.hom =
      (rightBaseChangeTensorIso f P.of x.base.obj).hom := rfl

end Quillen.FiniteProjectiveModule
