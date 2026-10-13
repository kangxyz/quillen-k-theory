/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforwardAcyclicity

/-! Original injective-resolution and higher-direct-image consumers for affine morphisms. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.AffinePushforwardAcyclicity

open Quillen

/-- Every chosen ambient injective resolution gives the same positive-degree exactness. -/
theorem original_resolution {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (M : Z.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (n : ℕ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) :=
  SchemeSheaf.affinePushforward_injectiveResolution_exact_succ f M I n

/-- Actual outgoing higher-direct-image maps vanish on quasicoherent coefficients. -/
theorem original_higher_map {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (M N : Z.Modules) [M.IsQuasicoherent] (s : M ⟶ N) (n : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived (n + 1)).map s = 0 :=
  (SchemeSheaf.isZero_rightDerived_pushforward_succ f M n).eq_of_src _ _

/-- Every ring map gives the vanishing, without a finiteness or flatness assumption. -/
theorem original_spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward (Spec.map φ)).rightDerived (n + 1)).obj M) :=
  SchemeSheaf.isZero_rightDerived_pushforward_succ (Spec.map φ) M n

end QuillenTest.AffinePushforwardAcyclicity
