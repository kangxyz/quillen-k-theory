/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.Algebra.Category.ModuleCat.Finite
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Quillen.GTheory.FiniteModules.ClosedSupport
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Principal quotient pushforward and scalar restriction

The functor is the restriction of `Scheme.Modules.pushforward` to the actual
coherent full subcategories. Its global-section comparison is with genuine
quotient-ring restriction of scalars.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open Quillen.FiniteModuleLocalization


open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
open FiniteModuleLocalization

variable (R : CommRingCat.{u}) (f : R)

variable [IsNoetherianRing R]

/-- The actual geometric pushforward/global-sections comparison square. -/
def coherentPushforwardSquare :
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.closedMap R
      (Ideal.span {f})) ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence
        (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f}))).functor ⋙ closedRestriction f :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec
      (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))))
      (AlgebraicGeometry.Scheme.Modules.pushforwardGlobalSectionsIso
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))


end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
