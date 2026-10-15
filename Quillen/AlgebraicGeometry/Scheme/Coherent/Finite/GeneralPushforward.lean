/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.AffineDetection
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Coherent direct image along arbitrary finite morphisms

The original module-sheaf pushforward along a finite morphism preserves
finite-type quasicoherent sheaves. Actual affine presentations and open base
change reduce this to finite restriction of scalars. Over locally noetherian
schemes this gives an exact coherent functor and its original G-theory map.
No proper direct-image or perfect-complex preservation assertion is made.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f]

/-- The canonical covariant G-map of the actual finite coherent direct image. -/
def coherentPushforwardGMap (n : ℕ) : G Z n →* G X n :=
  (coherentPushforwardExact f).smallKMap n

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
