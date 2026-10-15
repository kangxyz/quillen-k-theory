/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Original pullback comparisons on commuting squares

The comparison is built from composition and equality isomorphisms and preserves original
maps into and out of the ordered unit square.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules



noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable {U V Y X : Scheme.{u}} (a : U ⟶ Y) (j : Y ⟶ X) (c : U ⟶ V) (b : V ⟶ X)
  (h : a ≫ j = c ≫ b)
/-- The original pullback comparison for a genuinely commuting scheme square. -/
def pullbackSquareIso :
    AlgebraicGeometry.Scheme.Modules.pullback j ⋙ AlgebraicGeometry.Scheme.Modules.pullback a ≅
      AlgebraicGeometry.Scheme.Modules.pullback b ⋙ AlgebraicGeometry.Scheme.Modules.pullback c :=
  AlgebraicGeometry.Scheme.Modules.pullbackComp a j ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackCongr h ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp c b).symm
/-- The actual commuting-square comparison preserves the two ordered structure coordinates. -/
theorem pullbackSquareIso_unitSquare :
    (pullbackSquareIso a j c b h).hom.app
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯ SheafOfModules.unit X.ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback c).map (pullbackUnitSquareIso b).hom ≫
        (pullbackUnitSquareIso c).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackUnitSquareIso j).hom ≫
        (pullbackUnitSquareIso a).hom := by
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← pullbackUnitSquareIso_comp, Iso.inv_hom_id_app_assoc,
    pullbackUnitSquareIso_congr, pullbackUnitSquareIso_comp]
/-- Pullback-square transport retains the original morphism into the unit square. -/
theorem pullbackSquareIso_map_to_unitSquare {M : X.Modules}
    (φ : M ⟶ ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf)) :
    (AlgebraicGeometry.Scheme.Modules.pullback a).map
        ((AlgebraicGeometry.Scheme.Modules.pullback j).map φ) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback a).map (pullbackUnitSquareIso j).hom ≫
        (pullbackUnitSquareIso a).hom =
      (pullbackSquareIso a j c b h).hom.app M ≫
        (AlgebraicGeometry.Scheme.Modules.pullback c).map
          ((AlgebraicGeometry.Scheme.Modules.pullback b).map φ ≫
            (pullbackUnitSquareIso b).hom) ≫ (pullbackUnitSquareIso c).hom := by
  have hn := (pullbackSquareIso a j c b h).hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [← pullbackSquareIso_unitSquare a j c b h]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
/-- Pullback-square transport retains the original morphism out of the unit square. -/
theorem pullbackSquareIso_map_from_unitSquare {M : X.Modules}
    (φ : ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
      SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback b).obj M ≅
      SheafOfModules.unit V.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback a).map
        ((AlgebraicGeometry.Scheme.Modules.pullback j).map φ) ≫
      (pullbackSquareIso a j c b h).hom.app M ≫
        (AlgebraicGeometry.Scheme.Modules.pullback c).map e.hom ≫ (pullbackUnitIso c).hom =
      (pullbackSquareIso a j c b h).hom.app _ ≫
        (AlgebraicGeometry.Scheme.Modules.pullback c).map
          ((AlgebraicGeometry.Scheme.Modules.pullback b).map φ ≫ e.hom) ≫
            (pullbackUnitIso c).hom := by
  have hn := (pullbackSquareIso a j c b h).hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
end AlgebraicGeometry.Scheme.Modules
