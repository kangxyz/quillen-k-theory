/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforwardAcyclicity
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AcyclicPushforwardResolution

/-! # The original affine direct image of a quasicoherent injective resolution

The actual augmentation remains a quasi-isomorphism after direct image.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.SchemeSheaf

/-- Affine direct image preserves the original augmentation of every quasicoherent resolution. -/
theorem quasiIso_pushforward_injectiveResolution {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (M : Z.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map I.ι) :=
  quasiIso_pushforward_injectiveResolution_of_exact f M I
    (affinePushforward_injectiveResolution_exact_succ f M I)

/-- The original integer-indexed injective augmentation remains a quasi-isomorphism. -/
theorem quasiIso_pushforward_injectiveResolution_int {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (M : Z.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).map I.ι') :=
  quasiIso_pushforward_injectiveResolution_int_of_quasiIso f M I
    (quasiIso_pushforward_injectiveResolution f M I)

end Quillen.SchemeSheaf
