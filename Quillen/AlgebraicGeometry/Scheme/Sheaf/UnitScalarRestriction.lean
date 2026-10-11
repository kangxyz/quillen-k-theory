/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.UnitSections

/-! # Scalar presentations under original open restriction

Pullback trivializations pass to actual open restriction through the original comparison.
Further restriction retains the literal scalar section pulled back by the scheme map.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.SchemeSheaf
/-- A pullback trivialization determines the original open-restriction trivialization. -/
def restrictionUnitTrivialization {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (e : (Scheme.Modules.pullback j).obj M ≅
      SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor j).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app M ≪≫ e
/-- The original pullback scalar equation is retained on actual open restriction. -/
theorem restrictionUnitTrivialization_map {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {M N : Y.Modules} (f : M ⟶ N)
    (e : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (d : (Scheme.Modules.pullback j).obj N ≅ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(X, ⊤))
    (hf : (Scheme.Modules.pullback j).map f ≫ d.hom = e.hom ≫ unitMul X s) :
    (Scheme.Modules.restrictFunctor j).map f ≫ (restrictionUnitTrivialization j d).hom =
      (restrictionUnitTrivialization j e).hom ≫ unitMul X s := by
  dsimp only [restrictionUnitTrivialization, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality,
    Category.assoc, hf, Category.assoc]
/-- An actual unit trivialization restricts through the canonical restriction-unit isomorphism. -/
def restrictUnitTrivialization {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor j).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor j).mapIso e ≪≫ Scheme.Modules.restrictUnitIso j
/-- Restricting an original scalar equation pulls back precisely its original global section. -/
theorem restrictUnitTrivialization_map {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {M N : Y.Modules} (f : M ⟶ N)
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (d : N ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(Y, ⊤))
    (hf : f ≫ d.hom = e.hom ≫ unitMul Y s) :
    (Scheme.Modules.restrictFunctor j).map f ≫ (restrictUnitTrivialization j d).hom =
      (restrictUnitTrivialization j e).hom ≫ unitMul X (j.appTop.hom s) := by
  dsimp only [restrictUnitTrivialization, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hf, Functor.map_comp, Category.assoc,
    unitMul_restrict, Category.assoc]
end Quillen.SchemeSheaf
