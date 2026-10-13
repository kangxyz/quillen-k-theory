/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AcyclicDerivedPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforwardResolution

/-! # The actual bounded-below derived unit on a quasicoherent sheaf in degree zero

The original affine direct image of an actual injective resolution proves
that the actual right-derived unit is an isomorphism on single quasicoherent
sheaves. No replacement of this unit or perfection conclusion is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.SchemeSheaf
/-- The standard ambient derived category of module sheaves used by the actual unit. -/
local instance affineDerivedPushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The original right-derived direct-image unit is invertible on single quasicoherent sheaves. -/
theorem isIso_derivedPushforwardPlusUnit_single {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (M : Z.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus Z M)) :=
  isIso_derivedPushforwardPlusUnit_single_of_resolution f M (injectiveResolution M)
    (quasiIso_pushforward_injectiveResolution_int f M (injectiveResolution M))

end Quillen.SchemeSheaf
