/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Quillen.Aglib.AlgebraicGeometry.Modules.RankOne.Quotient

/-! # Pullback of actual scalar columns and quotient rows

The original restriction-to-pullback comparison preserves unit trivializations. Pulling back
scalar multiplication gives the original pullback section, preserving all signed rows.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open Quillen

noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction adjunction sends the unit trivialization to the original structure map. -/
theorem restrictUnitIso_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  rw [Adjunction.homEquiv_apply]
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change (f.appIso (f ⁻¹ᵁ U)).hom.hom
    ((Y.presheaf.map (homOfLE (f.image_preimage_le U)).op).hom x) = (f.app U).hom x
  have h : Y.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f ⁻¹ᵁ U)).hom = f.app U := by
    rw [AlgebraicGeometry.Scheme.Hom.appIso_hom', AlgebraicGeometry.Scheme.Hom.map_appLE,
      AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
  exact congrArg (fun k => CommRingCat.Hom.hom k x) h

/-- The original restriction-to-pullback comparison preserves the structure module. -/
theorem restrictFunctorIsoPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫ (pullbackUnitIso f).hom =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
  apply (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, restrictUnitIso_homEquiv]
  exact pullbackUnitIso_homEquiv f

/-- The original restriction-to-pullback comparison retains both ordered unit coordinates. -/
theorem restrictFunctorIsoPullback_unitSquare {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.app
        ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⨯
          SheafOfModules.unit Y.ringCatSheaf) ≫ (pullbackUnitSquareIso f).hom =
      (unitSquareRestrictionIso f).hom := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, pullbackUnitSquareIso_hom_fst, unitSquareRestrictionIso_fst,
      ← Category.assoc,
      ← (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality
        Limits.prod.fst, Category.assoc, restrictFunctorIsoPullback_unit]
  · rw [Category.assoc, pullbackUnitSquareIso_hom_snd, unitSquareRestrictionIso_snd,
      ← Category.assoc,
      ← (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality
        Limits.prod.snd, Category.assoc, restrictFunctorIsoPullback_unit]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of scalar multiplication retains the actual pulled-back section. -/
theorem unitMul_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (unitMul Y s) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f).hom ≫ unitMul X (f.appTop.hom s) := by
  apply (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, pullbackUnitIso_homEquiv,
    Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change (f.app U).hom (x * (Y.presheaf.map (homOfLE le_top).op).hom s) =
    (f.app U).hom x * (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom s)
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ f.app U =
      f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE,
      AlgebraicGeometry.Scheme.Hom.map_appLE, AlgebraicGeometry.Scheme.Hom.app_eq_appLE,
      AlgebraicGeometry.Scheme.Hom.appLE_map]
  exact congrArg (fun k => CommRingCat.Hom.hom k s) h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤))

/-- Pullback of the original graph column retains its two ordered coordinates. -/
theorem graphColumn_pullback :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (graphColumn (unitMul Y s)) ≫
      (pullbackUnitSquareIso f).hom =
      (pullbackUnitIso f).hom ≫ graphColumn (unitMul X (f.appTop.hom s)) := by
  apply prod.hom_ext
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_fst, graphColumn,
      prod.lift_fst, ← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_snd, graphColumn, prod.lift_snd,
      ← Functor.map_comp_assoc]
    exact unitMul_pullback f s

/-- Pullback of the original cograph column retains its two ordered coordinates. -/
theorem cographColumn_pullback :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (cographColumn (unitMul Y s)) ≫
      (pullbackUnitSquareIso f).hom =
      (pullbackUnitIso f).hom ≫ cographColumn (unitMul X (f.appTop.hom s)) := by
  apply prod.hom_ext
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_fst, cographColumn, prod.lift_fst,
      ← Functor.map_comp_assoc]
    exact unitMul_pullback f s
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_snd, cographColumn,
      prod.lift_snd, ← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]

/-- Pullback of the signed graph quotient retains the original pulled-back scalar. -/
theorem graphRow_pullback :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (graphRow (unitMul Y s)) ≫
      (pullbackUnitIso f).hom =
      (pullbackUnitSquareIso f).hom ≫ graphRow (unitMul X (f.appTop.hom s)) := by
  simp [graphRow, Preadditive.sub_comp, Preadditive.comp_sub, Functor.map_sub,
    Functor.map_comp, Category.assoc, unitMul_pullback]

/-- Pullback of the signed cograph quotient retains the original pulled-back scalar. -/
theorem cographRow_pullback :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (cographRow (unitMul Y s)) ≫
      (pullbackUnitIso f).hom =
      (pullbackUnitSquareIso f).hom ≫ cographRow (unitMul X (f.appTop.hom s)) := by
  simp [cographRow, Preadditive.sub_comp, Preadditive.comp_sub, Functor.map_sub,
    Functor.map_comp, Category.assoc, unitMul_pullback]

/-- Subtraction of scalars is subtraction of the original unit endomorphisms. -/
theorem unitMul_sub (Z : Scheme.{u}) (s t : Γ(Z, ⊤)) :
    unitMul Z (s - t) = unitMul Z s - unitMul Z t := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Z, U) at x
  change x * (Z.presheaf.map (homOfLE le_top).op).hom (s - t) =
    x * (Z.presheaf.map (homOfLE le_top).op).hom s -
      x * (Z.presheaf.map (homOfLE le_top).op).hom t
  rw [map_sub, mul_sub]

/-- The two graph coordinates give the literal difference. -/
theorem graphColumn_graphRow_unitMul (Z : Scheme.{u}) (s t : Γ(Z, ⊤)) :
    graphColumn (unitMul Z s) ≫ graphRow (unitMul Z t) = unitMul Z (s - t) := by
  simp [graphColumn, graphRow, Preadditive.comp_sub, unitMul_sub]

/-- The graph and cograph coordinates give the literal product minus one. -/
theorem graphColumn_cographRow_unitMul (Z : Scheme.{u}) (s t : Γ(Z, ⊤)) :
    graphColumn (unitMul Z s) ≫ cographRow (unitMul Z t) = unitMul Z (s * t - 1) := by
  simp [graphColumn, cographRow, Preadditive.comp_sub, unitMul_sub, unitMul_mul, unitMul_one]

/-- The cograph and graph coordinates give one minus the literal product. -/
theorem cographColumn_graphRow_unitMul (Z : Scheme.{u}) (s t : Γ(Z, ⊤)) :
    cographColumn (unitMul Z s) ≫ graphRow (unitMul Z t) = unitMul Z (1 - s * t) := by
  simp [cographColumn, graphRow, Preadditive.comp_sub, unitMul_sub, unitMul_mul, unitMul_one]

/-- The two cograph coordinates give the reverse literal difference. -/
theorem cographColumn_cographRow_unitMul (Z : Scheme.{u}) (s t : Γ(Z, ⊤)) :
    cographColumn (unitMul Z s) ≫ cographRow (unitMul Z t) = unitMul Z (t - s) := by
  simp [cographColumn, cographRow, Preadditive.comp_sub, unitMul_sub]

end AlgebraicGeometry.Scheme.Modules
