/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction

/-!
# Functoriality of vector-bundle restriction

Identity and composition isomorphisms for genuine open restriction lift through the fully faithful vector-bundle inclusion.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric identity comparison lifts to actual vector bundles. -/

def vectorBundleRestrictIdIso (X : Scheme.{u}) :
    vectorBundleRestrict (𝟙 X) ≅ 𝟭 (FiniteLocallyFree X) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι Scheme.Modules.restrictFunctorId)

/-- The geometric composition comparison lifts to actual vector bundles. -/

def vectorBundleRestrictCompIso {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    vectorBundleRestrict (i ≫ j) ≅ vectorBundleRestrict j ⋙ vectorBundleRestrict i :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree V).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι
      (Scheme.Modules.restrictFunctorComp i j))

end AlgebraicGeometry.Scheme.Modules
