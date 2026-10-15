/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianOpenBaseChange

/-!
# Original open restriction followed by direct image

The original restriction adjunction gives the localization unit. Nested open
immersions give natural smaller-open maps, preserving the actual composite
unit and the literal restriction on every open section. The unit is invertible
on its own chart, and cartesian open base change makes the smaller-open map
invertible on the other chart.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The original restriction followed by direct image along an open immersion. -/
def openLocalization {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    X.Modules ⥤ X.Modules := Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.pushforward j
/-- The original adjunction unit into localization at an open immersion. -/
def openLocalizationUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    𝟭 X.Modules ⟶ openLocalization j := (Scheme.Modules.restrictAdjunction j).unit
/-- Nested original restriction and direct image give the actual restriction-to-smaller-open map. -/
def openLocalizationMap {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules) :
    (openLocalization j).obj M ⟶ (openLocalization (a ≫ j)).obj M :=
  (Scheme.Modules.pushforward j).map
    ((Scheme.Modules.restrictAdjunction a).unit.app (M.restrict j)) ≫
  (Scheme.Modules.pushforwardComp a j).hom.app ((M.restrict j).restrict a) ≫
  (Scheme.Modules.pushforward (a ≫ j)).map
    ((Scheme.Modules.restrictFunctorComp a j).inv.app M)
/-- The actual localization arrow retains the original composite restriction unit. -/
theorem openLocalizationUnit_map {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules) :
    (openLocalizationUnit j).app M ≫ openLocalizationMap a j M =
      (openLocalizationUnit (a ≫ j)).app M := by
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Scheme.Modules.Hom.comp_app, openLocalizationMap,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    openLocalizationUnit, Scheme.Modules.restrictAdjunction_unit_app_app]
  rw [Scheme.Modules.restrict_map]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl
/-- Equality of the original open immersions gives the canonical localization comparison. -/
def openLocalizationCongr {U X : Scheme.{u}} {j k : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    openLocalization j ≅ openLocalization k := by
  subst h
  exact Iso.refl _
/-- The canonical equality comparison retains the original restriction unit. -/
theorem openLocalizationUnit_congr {U X : Scheme.{u}} {j k : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) (M : X.Modules) :
    (openLocalizationUnit j).app M ≫ (openLocalizationCongr h).hom.app M =
      (openLocalizationUnit k).app M := by
  subst h
  exact Category.comp_id _
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The original open-localization unit becomes invertible on its own open. -/
theorem isIso_restrict_openLocalizationUnit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor j).map ((openLocalizationUnit j).app M)) := by
  let ε := (Scheme.Modules.restrictAdjunction j).counit.app (M.restrict j)
  have : IsIso (((Scheme.Modules.restrictFunctor j).map
      ((openLocalizationUnit j).app M)) ≫ ε) := by
    change IsIso (((Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.restrictAdjunction j).unit.app M)) ≫ _)
    dsimp only [ε]
    erw [(Scheme.Modules.restrictAdjunction j).left_triangle_components]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ε
/-- The smaller-open restriction becomes invertible on the other member of its actual
cartesian open square. -/
theorem isIso_restrict_openLocalizationMap {W U V X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : IsPullback a b j k) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor k).map (openLocalizationMap a j M)) := by
  let := isIso_cartesianOpenBaseChangeUnit a b j k h
  have : IsIso ((Scheme.Modules.restrictFunctor k).map
      ((Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictAdjunction a).unit.app (M.restrict j)))) :=
    inferInstanceAs (IsIso ((Functor.whiskerRight (Scheme.Modules.restrictAdjunction a).unit
      (Scheme.Modules.pushforward j ⋙ Scheme.Modules.restrictFunctor k)).app (M.restrict j)))
  dsimp only [openLocalizationMap]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The nested original restriction map is natural in every original sheaf morphism. -/
theorem openLocalizationMap_naturality {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] {M N : X.Modules} (φ : M ⟶ N) :
    (openLocalization j).map φ ≫ openLocalizationMap a j N =
      openLocalizationMap a j M ≫ (openLocalization (a ≫ j)).map φ := by
  dsimp only [openLocalization, openLocalizationMap, Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp]
  erw [(Scheme.Modules.restrictAdjunction a).unit.naturality
    ((Scheme.Modules.restrictFunctor j).map φ)]
  rw [Functor.map_comp, Category.assoc]
  erw [(Scheme.Modules.pushforwardComp a j).hom.naturality_assoc
    ((Scheme.Modules.restrictFunctor a).map ((Scheme.Modules.restrictFunctor j).map φ))]
  rw [← Functor.map_comp]
  erw [(Scheme.Modules.restrictFunctorComp a j).inv.naturality φ]
  rw [Functor.map_comp]
  simp only [Category.assoc]
end AlgebraicGeometry.Scheme.Modules
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- The smaller original open has its actual inclusion into the larger localized open. -/
theorem openLocalization_image_le {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (V : X.Opens) :
    (a ≫ j) ''ᵁ ((a ≫ j) ⁻¹ᵁ V) ≤ j ''ᵁ (j ⁻¹ᵁ V) := by
  rw [Scheme.Hom.comp_image, Scheme.Hom.comp_preimage]
  exact j.image_mono (a.image_preimage_le _)
/-- Every component is the literal original sheaf restriction on the localized opens. -/
theorem openLocalizationMap_app {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules) (V : X.Opens) :
    (openLocalizationMap a j M).app V =
      M.presheaf.map (homOfLE (openLocalization_image_le a j V)).op := by
  simp only [openLocalizationMap, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app]
  rw [Scheme.Modules.restrict_map]
  erw [Category.id_comp]
  rw [← Functor.map_comp]
  rfl
end AlgebraicGeometry.Scheme.Modules
end
