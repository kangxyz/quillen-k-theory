/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.AffineDetection
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PushforwardIso
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
open Quillen.CoherentScheme


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.Finite
export AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite
  (affineLocallyFiniteType_pushforward affineLocallyFiniteType_pushforward_affine
  affinePresentationComparison coherentOpenBaseChange coherentPushforward
  coherentPushforwardExact coherentPushforward_additive
  coherentPushforward_affine_preservesFiniteColimits coherentPushforward_comp_inclusion
  coherentPushforward_preservesEpimorphisms coherentPushforward_preservesFiniteColimits
  coherentPushforward_preservesFiniteLimits exists_affine_presentation)
end Quillen.CoherentScheme.Finite

end



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
