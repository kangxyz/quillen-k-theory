/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Modules.Restriction.Overlap
public import Aglib.AlgebraicGeometry.Modules.Restriction.ZeroMorphisms
public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
public import Aglib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Rank-one columns compatible with original subobject gluing

The columns `(1, s)` and `(t, 1)` are original split-mono maps into the restricted
global structure-module square. Reciprocal coordinates on the actual pullback
produce their explicit unit transition and the exact inclusion compatibility
required by the existing subobject-gluing construction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- Both canonical unit restrictions agree on the original scheme pullback. -/

lemma restrictUnitIso_overlap {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (Scheme.Modules.restrictUnitIso k).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom =
    (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
        (Scheme.Modules.restrictUnitIso j).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.fst j k)).hom := by
  apply Scheme.Modules.hom_ext
  intro O
  ext x
  simp only [AlgebraicGeometry.Scheme.Modules.overlapRestrictIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  rw [← Functor.map_comp, ← Functor.map_comp]
  change ((X.presheaf.map (homOfLE _).op ≫
    (k.appIso ((pullback.snd j k) ''ᵁ O)).hom ≫
    ((pullback.snd j k).appIso O).hom).hom x) =
    (((j.appIso ((pullback.fst j k) ''ᵁ O)).hom ≫
    ((pullback.fst j k).appIso O).hom).hom x)
  have h : X.presheaf.map (homOfLE (show k ''ᵁ ((pullback.snd j k) ''ᵁ O) ≤
      j ''ᵁ ((pullback.fst j k) ''ᵁ O) from by
        simp only [← Scheme.Hom.comp_image, pullback.condition]; rfl)).op ≫
      (k.appIso _).hom ≫ ((pullback.snd j k).appIso O).hom =
      (j.appIso _).hom ≫ ((pullback.fst j k).appIso O).hom := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_comp_appLE, pullback.condition]
  exact congrArg (fun f => CommRingCat.Hom.hom f x) h

/-- Restriction preserves the actual binary-product comparison. -/

theorem restrict_prodComparison_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M N : X.Modules) :
    IsIso (prodComparison (Scheme.Modules.restrictFunctor j) M N) := inferInstance

/-- The actual split-mono column `(1, s)` into the restriction of the global unit square. -/

def firstColumn {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    (SheafOfModules.unit U.ringCatSheaf : U.Modules) ⟶
      (Scheme.Modules.restrictFunctor j).obj
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
          SheafOfModules.unit X.ringCatSheaf) := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  exact prod.lift (Scheme.Modules.restrictUnitIso j).inv
    (unitMul U s ≫ (Scheme.Modules.restrictUnitIso j).inv) ≫
    inv (prodComparison (Scheme.Modules.restrictFunctor j)
      (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf))

lemma firstColumn_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    firstColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      (Scheme.Modules.restrictUnitIso j).inv := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  simp [firstColumn, Category.assoc, inv_prodComparison_map_fst]

lemma firstColumn_snd {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    firstColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      unitMul U s ≫ (Scheme.Modules.restrictUnitIso j).inv := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  simp [firstColumn, Category.assoc, inv_prodComparison_map_snd]

instance firstColumn_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (s : Γ(U, ⊤)) : Mono (firstColumn j s) := by
  have h : Mono (firstColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst) := by
    rw [firstColumn_fst]
    infer_instance
  exact mono_of_mono (firstColumn j s) ((Scheme.Modules.restrictFunctor j).map prod.fst)

/-- The actual split-mono column `(s, 1)` into the restriction of the global unit square. -/

def secondColumn {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    (SheafOfModules.unit U.ringCatSheaf : U.Modules) ⟶
      (Scheme.Modules.restrictFunctor j).obj
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
          SheafOfModules.unit X.ringCatSheaf) := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  exact prod.lift (unitMul U s ≫ (Scheme.Modules.restrictUnitIso j).inv)
    (Scheme.Modules.restrictUnitIso j).inv ≫
    inv (prodComparison (Scheme.Modules.restrictFunctor j)
      (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf))

lemma secondColumn_snd {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    secondColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      (Scheme.Modules.restrictUnitIso j).inv := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  simp [secondColumn, Category.assoc, inv_prodComparison_map_snd]

lemma secondColumn_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    secondColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      unitMul U s ≫ (Scheme.Modules.restrictUnitIso j).inv := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  simp [secondColumn, Category.assoc, inv_prodComparison_map_fst]

instance secondColumn_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (s : Γ(U, ⊤)) : Mono (secondColumn j s) := by
  have h : Mono (secondColumn j s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd) := by
    rw [secondColumn_snd]
    infer_instance
  exact mono_of_mono (secondColumn j s) ((Scheme.Modules.restrictFunctor j).map prod.snd)

/-- The original rank-one transition given by an invertible overlap section. -/

def columnTransition {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (s : (Γ(CategoryTheory.Limits.pullback j k, ⊤))ˣ) :
    Scheme.Modules.restrict (SheafOfModules.unit U.ringCatSheaf) (pullback.fst j k) ≅
      Scheme.Modules.restrict (SheafOfModules.unit V.ringCatSheaf) (pullback.snd j k) :=
  Scheme.Modules.restrictUnitIso (pullback.fst j k) ≪≫ unitMulIso _ s ≪≫
    (Scheme.Modules.restrictUnitIso (pullback.snd j k)).symm

lemma restrictUnitIso_overlap_inv {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    (Scheme.Modules.restrictFunctor (pullback.fst j k)).map
        (Scheme.Modules.restrictUnitIso j).inv ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (Scheme.Modules.restrictUnitIso k).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom =
      (Scheme.Modules.restrictUnitIso (pullback.fst j k)).hom := by
  rw [restrictUnitIso_overlap]
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Reciprocal original overlap coordinates make the two actual columns compatible
with the displayed unit transition, as required by module-subobject gluing. -/

lemma columns_compatible {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (s : Γ(U, ⊤)) (t : Γ(V, ⊤))
    (v : (Γ(CategoryTheory.Limits.pullback j k, ⊤))ˣ)
    (hs : (pullback.fst j k).appTop.hom s = v)
    (ht : (pullback.snd j k).appTop.hom t = ↑v⁻¹) :
    (Scheme.Modules.restrictFunctor (pullback.fst j k)).map (firstColumn j s) ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
          SheafOfModules.unit X.ringCatSheaf) =
    (columnTransition j k v).hom ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map (secondColumn k t) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let F := Scheme.Modules.restrictFunctor k ⋙
    Scheme.Modules.restrictFunctor (pullback.snd j k)
  have hi (M N : X.Modules) : IsIso (prodComparison F M N) := inferInstance
  let := hi O O
  have hcancel : (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (Scheme.Modules.restrictUnitIso k).inv ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        (Scheme.Modules.restrictUnitIso k).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom =
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  apply (cancel_mono (prodComparison F O O)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, prodComparison_fst]
    change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map (firstColumn j s) ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app _ ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
          ((Scheme.Modules.restrictFunctor k).map prod.fst) = _
    have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
      (show O ⨯ O ⟶ O from prod.fst)
    dsimp only [Functor.comp_map] at hn
    rw [← hn,
      ← Category.assoc, ← Functor.map_comp, firstColumn_fst]
    change _ = (columnTransition j k v).hom ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map (secondColumn k t) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        ((Scheme.Modules.restrictFunctor k).map prod.fst)
    rw [← Functor.map_comp, secondColumn_fst]
    apply (cancel_mono ((Scheme.Modules.restrictFunctor (pullback.snd j k)).map
      (Scheme.Modules.restrictUnitIso k).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom)).mp
    dsimp only [O]
    simp only [Category.assoc, restrictUnitIso_overlap_inv]
    simp only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso,
      Functor.map_comp, Category.assoc, hcancel]
    rw [unitMul_restrict]
    simp only [Iso.inv_hom_id_assoc, ht]
    rw [← unitMul_mul]
    simp [unitMul_one]
  · simp only [Category.assoc, prodComparison_snd]
    change (Scheme.Modules.restrictFunctor (pullback.fst j k)).map (firstColumn j s) ≫
      (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.app _ ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
          ((Scheme.Modules.restrictFunctor k).map prod.snd) = _
    have hn := (AlgebraicGeometry.Scheme.Modules.overlapRestrictIso j k).hom.naturality
      (show O ⨯ O ⟶ O from prod.snd)
    dsimp only [Functor.comp_map] at hn
    rw [← hn,
      ← Category.assoc, ← Functor.map_comp, firstColumn_snd]
    change _ = (columnTransition j k v).hom ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map (secondColumn k t) ≫
      (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        ((Scheme.Modules.restrictFunctor k).map prod.snd)
    rw [← Functor.map_comp, secondColumn_snd]
    apply (cancel_mono ((Scheme.Modules.restrictFunctor (pullback.snd j k)).map
      (Scheme.Modules.restrictUnitIso k).hom ≫
      (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom)).mp
    dsimp only [O]
    simp only [Functor.map_comp, Category.assoc, restrictUnitIso_overlap_inv,
      columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso,
      hcancel, Iso.inv_hom_id]
    rw [unitMul_restrict, hs]
    simp only [Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
