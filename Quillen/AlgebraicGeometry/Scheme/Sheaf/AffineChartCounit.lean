/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineChartSections
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforward

/-! # The actual tilde counit on affine chart pushforwards

A chart with an affine coordinate projection has an invertible original counit.
The intermediate scheme and its projection need not be affine.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf
variable {R A : CommRingCat.{u}} {X : Scheme.{u}}
variable (a : R ⟶ A) (j : Spec A ⟶ X) (p : X ⟶ Spec R) (h : j ≫ p = Spec.map a)

include h in
/-- Actual affine chart pushforwards have an invertible original tilde counit. -/
theorem isIso_chartPushforward_counit (N : (Spec A).Modules) [N.IsQuasicoherent] :
    IsIso (((Scheme.Modules.pushforward p).obj
      ((Scheme.Modules.pushforward j).obj N)).fromTildeΓ) := by
  let e := (Scheme.Modules.pushforwardComp j p).app N ≪≫
    (Scheme.Modules.pushforwardCongr h).app N
  have hN := isQuasicoherent_pushforward a N
  have : ((Scheme.Modules.pushforward p).obj
      ((Scheme.Modules.pushforward j).obj N)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm hN
  infer_instance

end Quillen.SchemeSheaf
end

end
