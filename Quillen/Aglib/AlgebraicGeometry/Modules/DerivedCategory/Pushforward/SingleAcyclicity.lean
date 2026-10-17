/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Quillen.Aglib.CategoryTheory.Limits.Shapes.NatTransProduct
public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.Acyclic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Original derived direct-image comparisons for acyclic single sheaves

Invert the installed derived unit, retaining the actual single-complex comparison
and its naturality. A binary product of acyclic single sheaves is acyclic.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Use the standard derived category of actual module sheaves. -/
local instance derivedSingleComparisonStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The original derived unit identifies the derived image of an acyclic single sheaf. -/
def derivedPushforwardPlusSingleIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))] :
    (derivedPushforwardPlus f).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward f).obj M) :=
  (asIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))).symm ≪≫
    DerivedCategory.Plus.Q.mapIso (pushforwardSingleZeroPlusIso f M)

/-- The original installed unit followed by the acyclic comparison is the literal single map. -/
theorem derivedPushforwardPlusSingleIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))] :
    (derivedPushforwardPlusUnit f).app (singleZeroPlus X M) ≫
        (derivedPushforwardPlusSingleIso f M).hom =
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso f M).hom := by
  dsimp only [derivedPushforwardPlusSingleIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, Functor.mapIso_hom]
  simp

/-- The original termwise single comparison retains arbitrary original sheaf arrows. -/
theorem pushforwardSingleZeroPlusIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus.map
        ((CochainComplex.singleFunctorPlus X.Modules 0).map φ) ≫
        (pushforwardSingleZeroPlusIso f N).hom =
      (pushforwardSingleZeroPlusIso f M).hom ≫
        (CochainComplex.singleFunctorPlus Y.Modules 0).map
          ((Scheme.Modules.pushforward f).map φ) := by
  apply ObjectProperty.hom_ext
  exact (HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.pushforward f) (.up ℤ) 0).hom.naturality φ

/-- The acyclic single comparison is natural for the original sheaf morphism. -/
theorem derivedPushforwardPlusSingleIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (φ : M ⟶ N)
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))]
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X N))] :
    (derivedPushforwardPlus f).map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ) ≫
        (derivedPushforwardPlusSingleIso f N).hom =
      (derivedPushforwardPlusSingleIso f M).hom ≫
        (DerivedCategory.Plus.singleFunctor Y.Modules 0).map
          ((Scheme.Modules.pushforward f).map φ) := by
  apply (cancel_epi ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))).mp
  dsimp only [derivedPushforwardPlusSingleIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom]
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have h := (derivedPushforwardPlusUnit f).naturality
    ((CochainComplex.singleFunctorPlus X.Modules 0).map φ)
  change _ = _ at h
  erw [← h]
  simp only [Category.assoc]
  erw [IsIso.hom_inv_id_assoc]
  change DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
        ((CochainComplex.singleFunctorPlus X.Modules 0).map φ)) ≫
      DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso f N).hom =
    DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso f M).hom ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus Y.Modules 0).map
        ((Scheme.Modules.pushforward f).map φ))
  simpa only [Functor.map_comp] using
    congrArg DerivedCategory.Plus.Q.map (pushforwardSingleZeroPlusIso_naturality f φ)

end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Use the standard derived category of actual module sheaves. -/
local instance derivedSingleProductStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The original direct-image unit on a product of two acyclic single sheaves is invertible. -/
theorem isIso_derivedPushforwardPlusUnit_single_prod {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : X.Modules)
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M))]
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X N))] :
    IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X (M ⨯ N))) := by
  let : (DerivedCategory.Plus.Q (C := X.Modules)).Additive := by
    dsimp only [DerivedCategory.Plus.Q]
    infer_instance
  let : (DerivedCategory.Plus.Q (C := Y.Modules)).Additive := by
    dsimp only [DerivedCategory.Plus.Q]
    infer_instance
  let : (derivedPushforwardPlus f).Additive :=
    inferInstanceAs (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.Additive
  let α := whiskerLeft (CochainComplex.singleFunctorPlus X.Modules 0)
    (derivedPushforwardPlusUnit f)
  let : IsIso (α.app M) :=
    inferInstanceAs (IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X M)))
  let : IsIso (α.app N) :=
    inferInstanceAs (IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X N)))
  change IsIso (α.app (M ⨯ N))
  apply NatTrans.isIso_app_prod

end AlgebraicGeometry.Scheme.Modules
end
