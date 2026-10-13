/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechCounit
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineSectionsCone

/-! # The original two-term sheaf Cech cone

The actual signed sheaf difference and the explicit minus-one shift are retained.
The comparison with associated affine sections uses the original counits on both
terms and their naturality square; no homology of sections is assumed.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The shifted cone of the literal pushforward of the original signed sheaf difference. -/
def originalSheafCechComplex : CochainComplex (Spec R).Modules ℤ :=
  (CochainComplex.mappingCone
    ((single (Spec R).Modules (.up ℤ) 0).map
      ((Scheme.Modules.pushforward (projection R)).map
        (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
          (plusChart R) (minusChart R) (overlap_equation R) M))))⟦(-1 : ℤ)⟧

/-- The actual associated section cone reconstructs the original sheaf Cech cone. -/
def originalSheafCechSectionsIso [M.IsQuasicoherent] :
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
      (Quillen.ModuleComplex.linearMapCechComplex
        (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
          (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
            (plusChart R) (minusChart R) (overlap_equation R) M))).hom) ≅
      originalSheafCechComplex R M := by
  let S := (Scheme.Modules.pushforward (projection R)).obj
    ((openLocalization (plusChart R)).obj M ⨯ (openLocalization (minusChart R)).obj M)
  let T := (Scheme.Modules.pushforward (projection R)).obj
    ((openLocalization (laurentPlus R ≫ plusChart R)).obj M)
  have : IsIso S.fromTildeΓ := isIso_cechSourceCounit R M
  have : IsIso T.fromTildeΓ := isIso_cechOverlapCounit R M
  have : S.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  have : T.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  exact affineSectionsCechIso R ((Scheme.Modules.pushforward (projection R)).map
    (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
      (plusChart R) (minusChart R) (overlap_equation R) M))

end Quillen.Scheme.ProjectiveLine
end

end
