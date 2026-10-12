/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineChartCounit
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechSections
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TildeExact
public import Quillen.CategoryTheory.Limits.NatTransProduct

/-! # Original counits on the two projective-line Cech terms

The two actual ordinary pushforward terms are reconstructed by their original
tilde counits. This does not assume quasicoherence of the projection direct image
of the input sheaf.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.Scheme.ProjectiveLine
/-- Invertibility of the original affine counit passes through the actual binary product. -/
private theorem isIso_productCounit (R : CommRingCat.{u})
    (M N : (Spec R).Modules) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    IsIso (M ⨯ N).fromTildeΓ := by
  let : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
    (tilde.adjunction (R := R)).isRightAdjoint
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app M) :=
    inferInstanceAs (IsIso M.fromTildeΓ)
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app N) :=
    inferInstanceAs (IsIso N.fromTildeΓ)
  exact NatTrans.isIso_app_prod _ _ Scheme.Modules.fromTildeΓNatTrans M N


open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) [M.IsQuasicoherent]

/-- The original product term of the pushed Cech sequence has an invertible counit. -/
theorem isIso_cechSourceCounit :
    IsIso (((Scheme.Modules.pushforward (projection R)).obj
      ((openLocalization (plusChart R)).obj M ⨯
        (openLocalization (minusChart R)).obj M)).fromTildeΓ) := by
  let A := (openLocalization (plusChart R)).obj M
  let B := (openLocalization (minusChart R)).obj M
  let F := Scheme.Modules.pushforward (projection R)
  have : IsIso (F.obj A).fromTildeΓ :=
    isIso_chartPushforward_counit (CommRingCat.ofHom Polynomial.C)
      (plusChart R) (projection R) (plusChart_projection R) (M.restrict (plusChart R))
  have : IsIso (F.obj B).fromTildeΓ :=
    isIso_chartPushforward_counit (CommRingCat.ofHom Polynomial.C)
      (minusChart R) (projection R) (minusChart_projection R) (M.restrict (minusChart R))
  have : IsIso (F.obj A ⨯ F.obj B).fromTildeΓ := isIso_productCounit R _ _
  have hqc : (F.obj A ⨯ F.obj B).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  have : (F.obj (A ⨯ B)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (PreservesLimitPair.iso F A B).symm hqc
  infer_instance

/-- The actual pushed overlap term has an invertible original counit. -/
theorem isIso_cechOverlapCounit :
    IsIso (((Scheme.Modules.pushforward (projection R)).obj
      ((openLocalization (laurentPlus R ≫ plusChart R)).obj M)).fromTildeΓ) :=
  isIso_chartPushforward_counit (CommRingCat.ofHom LaurentPolynomial.C)
    (laurentPlus R ≫ plusChart R) (projection R)
    (nestedProjection (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (CommRingCat.ofHom LaurentPolynomial.C) (Quillen.LaurentProjector.positive_constants R)
      (plusChart R) (projection R) (plusChart_projection R))
    (M.restrict (laurentPlus R ≫ plusChart R))

end Quillen.Scheme.ProjectiveLine
end

end
