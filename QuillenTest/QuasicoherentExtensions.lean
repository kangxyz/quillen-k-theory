/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.QuasicoherentExtensions
public import Mathlib.Data.ZMod.Basic


/-! # Original counit and restriction consumers of QC extension closure -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.QuasicoherentExtensions


/-- Both inverse laws retain the actual middle affine counit. -/
theorem original_middle_counit_inverse (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    ∃ a : S.X₂ ⟶ (tilde.functor R).obj (moduleSpecΓFunctor.obj S.X₂),
      S.X₂.fromTildeΓ ≫ a = 𝟙 _ ∧ a ≫ S.X₂.fromTildeΓ = 𝟙 _ := by
  have := AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_shortExact R hS
  exact ⟨inv S.X₂.fromTildeΓ, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- The reconstructed middle arrow commutes with the original inclusion and
quotient maps; no chosen alternate affine presentation appears. -/
theorem original_middle_counit_squares (R : CommRingCat.{u})
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    IsIso S.X₂.fromTildeΓ ∧
      (tilde.functor R).map (moduleSpecΓFunctor.map S.f) ≫ S.X₂.fromTildeΓ =
        S.X₁.fromTildeΓ ≫ S.f ∧
      (tilde.functor R).map (moduleSpecΓFunctor.map S.g) ≫ S.X₃.fromTildeΓ =
        S.X₂.fromTildeΓ ≫ S.g := by
  exact ⟨AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_shortExact R hS,
    Scheme.Modules.fromTildeΓNatTrans.naturality S.f,
    Scheme.Modules.fromTildeΓNatTrans.naturality S.g⟩

/-- The standard intrinsic property interface can be consumed directly, on
arbitrary schemes with no compactness or noetherian hypothesis. -/
theorem original_intrinsic_extension_property {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : (SheafOfModules.isQuasicoherent X.ringCatSheaf) S.X₁)
    (h₃ : (SheafOfModules.isQuasicoherent X.ringCatSheaf) S.X₃) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) S.X₂ :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_X₂_of_shortExact hS h₁ h₃

/-- Any actual open restriction of the original extension remains QC. -/
theorem original_open_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    ((Scheme.Modules.restrictFunctor j).obj S.X₂).IsQuasicoherent := by
  have := AlgebraicGeometry.Scheme.Modules.quasicoherent_of_shortExact hS
  exact Scheme.Modules.isQuasicoherent_restrictFunctor j S.X₂

local instance emptyAffineGlobalSectionsIsRightAdjoint :
    (moduleSpecΓFunctor (R := CommRingCat.of (ZMod 1))).IsRightAdjoint :=
  AlgebraicGeometry.Scheme.Modules.AffineCech.globalSections_isRightAdjoint _

/-- The zero-ring affine case includes the original counit and actual
short exact global-section sequence, with arbitrary original middle sheaf. -/
theorem empty_affine_original_counit
    {S : ShortComplex (Spec (.of (ZMod 1))).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent ∧ IsIso S.X₂.fromTildeΓ ∧
      (S.map (moduleSpecΓFunctor (R := CommRingCat.of (ZMod 1)))).ShortExact :=
  ⟨AlgebraicGeometry.Scheme.Modules.quasicoherent_of_shortExact hS,
    AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_shortExact _ hS,
    AlgebraicGeometry.Scheme.Modules.AffineCech.shortExact_globalSections_of_quasicoherent_kernel
      hS⟩
end QuillenTest.QuasicoherentExtensions
