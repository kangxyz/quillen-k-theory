/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RestrictionSquare
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneQuotient

/-!
# Rank-one columns under actual open restriction

A rank-one subobject with a specified original chart inclusion retains that graph or cograph
column under an actual commuting square of open immersions. Both projection equations are
preserved.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
variable {U V Y X : Scheme.{u}} (a : U ⟶ Y) (j : Y ⟶ X) (c : U ⟶ V) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c] [IsOpenImmersion b]
  (h : a ≫ j = c ≫ b) (M : X.Modules)
  (e : M.restrict b ≅ SheafOfModules.unit V.ringCatSheaf)

/-- The original chart trivialization transported through the actual restriction square. -/
def restrictionSquareLineIso : (M.restrict j).restrict a ≅
    SheafOfModules.unit U.ringCatSheaf :=
  (restrictionSquareIso a j c b h).app M ≪≫
    (Scheme.Modules.restrictFunctor c).mapIso e ≪≫ Scheme.Modules.restrictUnitIso c

lemma restrictionSquare_firstColumn
    (i : M ⟶ ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf)) (s : Γ(V, ⊤))
    (hi : (Scheme.Modules.restrictFunctor b).map i = e.hom ≫ firstColumn b s) :
    (Scheme.Modules.restrictFunctor a).map
        ((Scheme.Modules.restrictFunctor j).map i ≫ (unitSquareRestrictionIso j).hom) =
      (restrictionSquareLineIso a j c b h M e).hom ≫ firstColumn a (c.appTop.hom s) := by
  have hf : (Scheme.Modules.restrictFunctor b).map (i ≫ prod.fst) ≫
      (Scheme.Modules.restrictUnitIso b).hom = e.hom := by
    rw [Functor.map_comp, hi]
    simp only [Category.assoc]
    rw [reassoc_of% (firstColumn_fst b s), Iso.inv_hom_id, Category.comp_id]
  have hs : (Scheme.Modules.restrictFunctor b).map (i ≫ prod.snd) ≫
      (Scheme.Modules.restrictUnitIso b).hom = e.hom ≫ unitMul V s := by
    rw [Functor.map_comp, hi]
    simp only [Category.assoc]
    rw [reassoc_of% (firstColumn_snd b s)]
    simp only [Iso.inv_hom_id, Category.comp_id]
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor a)
    (prodIsProd (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf))).hom_ext
  rintro (_ | _)
  · change _ ≫ (Scheme.Modules.restrictFunctor a).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor a).map prod.fst
    rw [Category.assoc, firstColumn_fst]
    apply (cancel_mono (Scheme.Modules.restrictUnitIso a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Category.assoc, unitSquareRestrictionIso_fst,
      ← Category.assoc, ← Functor.map_comp]
    rw [← restrictionSquareIso_unit_map a j c b h (i ≫ prod.fst)]
    rw [hf]
    rfl
  · change _ ≫ (Scheme.Modules.restrictFunctor a).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor a).map prod.snd
    rw [Category.assoc, firstColumn_snd]
    apply (cancel_mono (Scheme.Modules.restrictUnitIso a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Category.assoc, unitSquareRestrictionIso_snd,
      ← Category.assoc, ← Functor.map_comp]
    rw [← restrictionSquareIso_unit_map a j c b h (i ≫ prod.snd)]
    rw [hs, Functor.map_comp, Category.assoc, unitMul_restrict]
    simp only [restrictionSquareLineIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc]

lemma restrictionSquare_secondColumn
    (i : M ⟶ ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf)) (s : Γ(V, ⊤))
    (hi : (Scheme.Modules.restrictFunctor b).map i = e.hom ≫ secondColumn b s) :
    (Scheme.Modules.restrictFunctor a).map
        ((Scheme.Modules.restrictFunctor j).map i ≫ (unitSquareRestrictionIso j).hom) =
      (restrictionSquareLineIso a j c b h M e).hom ≫ secondColumn a (c.appTop.hom s) := by
  have hf : (Scheme.Modules.restrictFunctor b).map (i ≫ prod.snd) ≫
      (Scheme.Modules.restrictUnitIso b).hom = e.hom := by
    rw [Functor.map_comp, hi]
    simp only [Category.assoc]
    rw [reassoc_of% (secondColumn_snd b s), Iso.inv_hom_id, Category.comp_id]
  have hs : (Scheme.Modules.restrictFunctor b).map (i ≫ prod.fst) ≫
      (Scheme.Modules.restrictUnitIso b).hom = e.hom ≫ unitMul V s := by
    rw [Functor.map_comp, hi]
    simp only [Category.assoc]
    rw [reassoc_of% (secondColumn_fst b s)]
    simp only [Iso.inv_hom_id, Category.comp_id]
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor a)
    (prodIsProd (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf))).hom_ext
  rintro (_ | _)
  · change _ ≫ (Scheme.Modules.restrictFunctor a).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor a).map prod.fst
    rw [Category.assoc, secondColumn_fst]
    apply (cancel_mono (Scheme.Modules.restrictUnitIso a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Category.assoc, unitSquareRestrictionIso_fst,
      ← Category.assoc, ← Functor.map_comp]
    rw [← restrictionSquareIso_unit_map a j c b h (i ≫ prod.fst)]
    rw [hs, Functor.map_comp, Category.assoc, unitMul_restrict]
    simp only [restrictionSquareLineIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc]
  · change _ ≫ (Scheme.Modules.restrictFunctor a).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor a).map prod.snd
    rw [Category.assoc, secondColumn_snd]
    apply (cancel_mono (Scheme.Modules.restrictUnitIso a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, Category.assoc, unitSquareRestrictionIso_snd,
      ← Category.assoc, ← Functor.map_comp]
    rw [← restrictionSquareIso_unit_map a j c b h (i ≫ prod.snd)]
    rw [hf]
    rfl

end Quillen.SchemeSheaf
