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
# Functoriality of coherent restriction

The actual finite-type sheaf restrictions along open immersions retain the original identity and composition comparisons.
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- The geometric identity comparison lifts to actual coherent sheaves. -/

def coherentRestrictionIdIso (X : Scheme.{u}) :
    finiteTypeSheavesRestriction (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) Scheme.Modules.restrictFunctorId)

/-- The geometric composition comparison lifts to actual coherent sheaves. -/

def coherentRestrictionCompIso {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    finiteTypeSheavesRestriction (i ≫ j) ≅
      finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesRestriction i :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules V)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X)
      (Scheme.Modules.restrictFunctorComp i j))

end AlgebraicGeometry.Scheme.Modules.Coherent
