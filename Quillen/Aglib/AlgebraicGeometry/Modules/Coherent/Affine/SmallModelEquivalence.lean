/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-!
# Equivalences of affine coherent small models

Global sections and the identity-on-sheaves affine comparison induce genuine equivalences of the categorical small models.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

instance affineGlobalSectionsSmall_isEquivalence :
    ((affineGlobalSectionsExact R).smallModel).toFunctor.IsEquivalence := by
  change (((equivSmallModel.{u} (AffineFiniteType R)).inverse ⋙
    (affineFiniteTypeModuleEquivalence R).functor) ⋙
    (equivSmallModel.{u} (FiniteModule.{u, u} R)).functor).IsEquivalence
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

instance coherentToAffineSmall_isEquivalence :
    ((coherentToAffineExact R).smallModel).toFunctor.IsEquivalence := by
  change (((equivSmallModel.{u} (FiniteTypeSheaves (Spec R))).inverse ⋙
    (finiteTypeSheavesAffineEquivalence R).functor) ⋙
    (equivSmallModel.{u} (AffineFiniteType R)).functor).IsEquivalence
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
