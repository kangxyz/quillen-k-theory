/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Affine

/-!
# Acyclicity of an affine direct image for a further direct image

For affine `j` and affine `j ≫ f`, the literal single sheaf `j_* M` is acyclic
for the installed bounded-below direct-image unit of `f`, when `M` is
quasicoherent. The proof uses the original composite-unit comparison and
ordinary single-complex isomorphism.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Use the installed standard derived category of actual module sheaves. -/
local instance affineCompositeDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- A single affine direct image is acyclic for a second map when the composite is affine. -/
theorem isIso_derivedPushforwardPlusUnit_pushforward_single {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (f : Y ⟶ Z) [IsAffineHom j] [IsAffineHom (j ≫ f)]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedPushforwardPlusUnit f).app
      (singleZeroPlus Y ((Scheme.Modules.pushforward j).obj M))) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ (pushforwardSingleZeroPlusIso j M)]
  let K := singleZeroPlus X M
  let : IsIso ((Scheme.Modules.pushforward j).rightDerivedFunctorPlusUnit.app K) :=
    isIso_derivedPushforwardPlusUnit_single j M
  let := isIso_derivedPushforwardPlusUnit_single (j ≫ f) M
  have h := derivedPushforwardPlusCompIso_unit j f K
  have : IsIso ((Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward j) (Scheme.Modules.pushforward f)).app K) := by
    have : IsIso ((derivedPushforwardPlusUnit (j ≫ f)).app K ≫
        (derivedPushforwardPlusCompIso j f).hom.app (DerivedCategory.Plus.Q.obj K)) :=
      inferInstance
    rw [h] at this
    exact (isIso_comp_left_iff _ _).mp this
  rw [Functor.rightDerivedFunctorPlusCompUnit_app] at this
  exact (isIso_comp_right_iff _ _).mp this

end AlgebraicGeometry.Scheme.Modules
