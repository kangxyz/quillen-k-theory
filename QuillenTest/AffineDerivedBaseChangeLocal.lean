/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChangeLocal

/-! # Original affine-morphism mate and installed single-pullback unit consumers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.SchemeSheaf
namespace QuillenTest.AffineDerivedBaseChangeLocal

open Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The actual standard module-sheaf derived categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
/-- The original flat-pullback unit identifies the literal single-complex pullback map. -/
theorem original_pullback_single_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (M : Y.Modules) :
    (Scheme.Modules.pullback f).rightDerivedFunctorPlusUnit.app (singleZeroPlus Y M) ≫
        (derivedFlatPullbackPlusSingleIso f M).hom =
      DerivedCategory.Plus.Q.map (pullbackSingleZeroPlusIso f M).hom :=
  derivedFlatPullbackPlusSingleIso_unit f M
variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [IsAffineHom f] [Flat j]
  (M : U.Modules) [M.IsQuasicoherent]
/-- The original affine-morphism mate has an inverse without affine ambient schemes. -/
theorem original_affine_morphism_inverse :
    ∃ r, (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) ≫ r = 𝟙 _ ∧
      r ≫ (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) = 𝟙 _ := by
  have := isIso_derivedFlatBaseChangeMap_affineHom_single a b f j h M
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
/-- The inverse of the actual mate retains naturality in an arbitrary QC sheaf arrow. -/
theorem original_inverse_naturality (N : U.Modules) [N.IsQuasicoherent] (φ : M ⟶ N) :
    letI := flat_cartesian_baseChange a b f j h
    letI := isIso_derivedFlatBaseChangeMap_affineHom_single a b f j h M
    letI := isIso_derivedFlatBaseChangeMap_affineHom_single a b f j h N
    inv ((derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
      (derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus j).map
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).map φ) =
    (derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b).map
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).map φ) ≫
      inv ((derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj N)) := by
  let := flat_cartesian_baseChange a b f j h
  have := isIso_derivedFlatBaseChangeMap_affineHom_single a b f j h M
  have := isIso_derivedFlatBaseChangeMap_affineHom_single a b f j h N
  apply (cancel_epi ((derivedFlatBaseChangeMap a b f j h).app
    ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M))).mp
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← (derivedFlatBaseChangeMap a b f j h).naturality_assoc]
  simp
end QuillenTest.AffineDerivedBaseChangeLocal
