/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Quillen.GTheory.FiniteModules.RestrictionScalars
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-! # The unchanged sheaf direct image along a finite affine map preserves coherence and is exact.
  The public G-map is explicitly formed in the original upper universe, distinct from the
  lower-universe affine model. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.FiniteAffine
export AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
  (affineLocallyFiniteType_pushforward coherentPushforward coherentPushforwardExact
  coherentPushforwardSquare coherentPushforward_additive coherentPushforward_comp_inclusion
  coherentPushforward_preservesFiniteColimits coherentPushforward_preservesFiniteLimits)
end Quillen.CoherentScheme.FiniteAffine

end




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite)

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- Covariant finite affine pushforward on the original public scheme G-groups. -/
def pushforwardG (n : ℕ) : G (Spec S) n →* G (Spec R) n :=
  (coherentPushforwardExact φ hφ).smallKMap.{u+1} n

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.Affine
