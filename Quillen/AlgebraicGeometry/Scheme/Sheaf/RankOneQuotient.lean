/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.Limits.SplitColumnCokernel
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneGluing

/-! # Original quotient rows for a two-chart rank-one subline

The canonical unit-square restriction identifies the original columns with split graph columns.
The quotient rows `(-s, 1)` and `(-1, t)` agree on the genuine overlap after multiplying by the
inverse transition unit. All comparisons retain the original module-sheaf restriction maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf

/-- Canonical restriction of the unit square to the original chart unit square. -/
def unitSquareRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).obj
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯ SheafOfModules.unit X.ringCatSheaf) ≅
      ((SheafOfModules.unit U.ringCatSheaf : U.Modules) ⨯ SheafOfModules.unit U.ringCatSheaf) := by
  let := restrict_prodComparison_isIso j (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf)
  exact asIso (prodComparison (Scheme.Modules.restrictFunctor j)
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      prod.mapIso (Scheme.Modules.restrictUnitIso j) (Scheme.Modules.restrictUnitIso j)

/-- The original positive column becomes the literal graph column. -/
lemma firstColumn_unitSquareRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    firstColumn j s ≫ (unitSquareRestrictionIso j).hom = graphColumn (unitMul U s) := by
  apply prod.hom_ext
  · simp [unitSquareRestrictionIso, graphColumn, Category.assoc]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k => k ≫ (Scheme.Modules.restrictUnitIso j).hom) (firstColumn_fst j s)
  · simp [unitSquareRestrictionIso, graphColumn, Category.assoc]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k => k ≫ (Scheme.Modules.restrictUnitIso j).hom) (firstColumn_snd j s)

/-- The original negative column becomes the exchanged graph column. -/
lemma secondColumn_unitSquareRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    secondColumn j s ≫ (unitSquareRestrictionIso j).hom = cographColumn (unitMul U s) := by
  apply prod.hom_ext
  · simp [unitSquareRestrictionIso, cographColumn, Category.assoc]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k => k ≫ (Scheme.Modules.restrictUnitIso j).hom) (secondColumn_fst j s)
  · simp [unitSquareRestrictionIso, cographColumn, Category.assoc]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k => k ≫ (Scheme.Modules.restrictUnitIso j).hom) (secondColumn_snd j s)

/-- The canonical square comparison preserves the first projection. -/
lemma unitSquareRestrictionIso_fst {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (unitSquareRestrictionIso j).hom ≫ prod.fst =
      (Scheme.Modules.restrictFunctor j).map prod.fst ≫
          (Scheme.Modules.restrictUnitIso j).hom := by
  simp [unitSquareRestrictionIso, Category.assoc]

/-- The canonical square comparison preserves the second projection. -/
lemma unitSquareRestrictionIso_snd {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (unitSquareRestrictionIso j).hom ≫ prod.snd =
      (Scheme.Modules.restrictFunctor j).map prod.snd ≫ (Scheme.Modules.restrictUnitIso j).hom := by
  simp [unitSquareRestrictionIso, Category.assoc]

/-- The original chart quotient row with coefficients `(-s, 1)`. -/
def firstRow {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    (Scheme.Modules.restrictFunctor j).obj
      ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯ SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit U.ringCatSheaf :=
  (unitSquareRestrictionIso j).hom ≫ graphRow (unitMul U s)

/-- The original chart quotient row with coefficients `(-1, s)`. -/
def secondRow {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    (Scheme.Modules.restrictFunctor j).obj
      ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯ SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.unit U.ringCatSheaf :=
  (unitSquareRestrictionIso j).hom ≫ cographRow (unitMul U s)

/-- The positive quotient row in the original restricted product projections. -/
lemma firstRow_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    firstRow j s =
      (Scheme.Modules.restrictFunctor j).map prod.snd ≫ (Scheme.Modules.restrictUnitIso j).hom -
        (Scheme.Modules.restrictFunctor j).map prod.fst ≫
          (Scheme.Modules.restrictUnitIso j).hom ≫ unitMul U s := by
  simp only [firstRow, graphRow, Preadditive.comp_sub, ← Category.assoc,
    unitSquareRestrictionIso_fst, unitSquareRestrictionIso_snd]

/-- The negative quotient row in the original restricted product projections. -/
lemma secondRow_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤)) :
    secondRow j s =
      (Scheme.Modules.restrictFunctor j).map prod.snd ≫
          (Scheme.Modules.restrictUnitIso j).hom ≫ unitMul U s -
        (Scheme.Modules.restrictFunctor j).map prod.fst ≫
          (Scheme.Modules.restrictUnitIso j).hom := by
  simp only [secondRow, cographRow, Preadditive.comp_sub, ← Category.assoc,
    unitSquareRestrictionIso_fst, unitSquareRestrictionIso_snd]


/-- Reciprocal chart coordinates give the inverse-unit transition for the literal quotient rows. -/
lemma rows_compatible {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (s : Γ(U, ⊤)) (t : Γ(V, ⊤))
    (v : (Γ(pullback j k, ⊤))ˣ)
    (hs : (pullback.fst j k).appTop.hom s = ↑v)
    (ht : (pullback.snd j k).appTop.hom t = ↑v⁻¹) :
    (Scheme.Modules.restrictFunctor (pullback.fst j k)).map (firstRow j s) ≫
        (columnTransition j k v⁻¹).hom =
      (Quillen.CoherentScheme.overlapRestrictIso j k).hom.app
          ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯ SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map (secondRow k t) := by
  apply (cancel_mono (Scheme.Modules.restrictUnitIso (pullback.snd j k)).hom).mp
  simp only [columnTransition, Iso.trans_hom, Iso.symm_hom, unitMulIso,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [firstRow_eq, secondRow_eq, Functor.map_sub, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
  have hf := (Quillen.CoherentScheme.overlapRestrictIso j k).hom.naturality
    (show ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf) ⟶ SheafOfModules.unit X.ringCatSheaf from prod.fst)
  have hg := (Quillen.CoherentScheme.overlapRestrictIso j k).hom.naturality
    (show ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf) ⟶ SheafOfModules.unit X.ringCatSheaf from prod.snd)
  dsimp only [Functor.comp_map] at hf hg
  rw [reassoc_of% (unitMul_restrict (pullback.fst j k) s),
    unitMul_restrict (pullback.snd j k) t]
  rw [← reassoc_of% hf, ← reassoc_of% hg]
  rw [reassoc_of% (restrictUnitIso_overlap j k), restrictUnitIso_overlap j k]
  rw [hs, ht, ← unitMul_mul]
  simp only [Units.mul_inv, unitMul_one, Category.comp_id]

end Quillen.SchemeSheaf
