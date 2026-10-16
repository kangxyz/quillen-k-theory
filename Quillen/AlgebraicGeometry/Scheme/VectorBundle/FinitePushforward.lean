/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Pushforward.Finite

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KTheory
public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteType
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The finite flat vector-bundle K-map

The actual finite flat vector-bundle direct image and its exactness are supplied by the local Aglib candidate, with a locally noetherian target. This downstream leaf forms the canonical map on the original vector-bundle K-groups.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- The canonical finite flat covariant map on vector-bundle K-theory. -/
def schemeKPushforward (n : ℕ) : SchemeK Z n →* SchemeK X n :=
  (vectorBundlePushforwardExact f).smallKMap n

end AlgebraicGeometry.Scheme.Modules
