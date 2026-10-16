/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# Small exact models of vector bundles

For an arbitrary scheme, finite locally free module sheaves have a categorical model in universe u + 1 with the transported ambient exact structure.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual vector-bundle category is essentially small in `u + 1`. -/

instance vectorBundle_essentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} (FiniteLocallyFree X) := by
  infer_instance

/-- A genuine small category equivalent to finite locally free sheaves. -/

abbrev SmallVectorBundle (X : Scheme.{u}) : Type (u + 1) :=
  SmallModel.{u + 1} (FiniteLocallyFree X)

/-- The exact structure transported to the actual categorical small model. -/

abbrev smallVectorBundleExactStructure (X : Scheme.{u}) :
    ExactStructure (SmallVectorBundle X) :=
  CategoryTheory.ExactCategory.ExactStructure.smallModel.{u + 1} (vectorBundleExactStructure X)

/-- The exact realization of small-model objects as actual vector bundles. -/

def smallVectorBundleToSheaves (X : Scheme.{u}) :
    ExactFunctor (smallVectorBundleExactStructure X) (sheafExactStructure X) :=
  (CategoryTheory.ExactCategory.ExactStructure.smallModelToOriginal.{u + 1}
    (vectorBundleExactStructure X)).comp
    (vectorBundleExactInclusion X)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual exact functor from the public small model to vector bundles. -/

abbrev smallVectorBundleToOriginal (X : Scheme.{u}) :
    ExactFunctor (smallVectorBundleExactStructure X) (vectorBundleExactStructure X) :=
  CategoryTheory.ExactCategory.ExactStructure.smallModelToOriginal.{u + 1}
    (vectorBundleExactStructure X)

end AlgebraicGeometry.Scheme.Modules
