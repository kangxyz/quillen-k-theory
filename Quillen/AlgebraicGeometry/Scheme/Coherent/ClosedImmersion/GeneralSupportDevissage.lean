/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Filtration

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Nilpotence
public import Quillen.AlgebraicGeometry.Scheme.Coherent.GlobalLocalization
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Subcategory
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Functor
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Refinement
public import Quillen.Devissage.Homotopical
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Actual closed-support dévissage on a noetherian scheme

The finite filtration comes from the actual epimorphic closed pullback unit.
Its kernels vanish after finitely many steps by the proved affine ideal-power
and finite-cover argument. The resulting filtration is transported through
the genuine supported-coherent small presentation.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The canonical annihilated-object inclusion is a genuine homotopical
K-equivalence onto the actual compatible supported term. -/
def supportDevissageKEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled i)).K n ≃*
      CoherentGlobalSupportedG (openMap i) n :=
  Devissage.KEquiv (supportKilled i) (supportFiltrationHypothesis i) n

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
