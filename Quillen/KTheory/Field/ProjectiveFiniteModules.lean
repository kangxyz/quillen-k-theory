/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjective
public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Quillen.CategoryTheory.SmallModel.CommonAmbientNaturality

/-!
# Finite projectives and the actual finite-module Q-groups over a field

The forward functor forgets only the projectivity certificate. Its inverse uses
projectivity of vector spaces over a field. Both functors preserve the actual
ambient short exact sequences, and the forward K-map is the resulting
equivalence. The upper-universe comparison uses the existing SmallModel
equivalence with its actual common-ambient Q-map.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteProjectiveModule

variable (F : Type u) [Field F]

/-- The literal inclusion of finite projectives into finite modules. -/
def toFiniteModule : Category.{u, v} F ⥤ FGModuleCat.{v} F :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- Every finite-dimensional vector space is projective; the carrier is unchanged. -/
def fromFiniteModule : FGModuleCat.{v} F ⥤ Category.{u, v} F :=
  ObjectProperty.ιOfLE (fun _ h => ⟨h, inferInstance⟩)

instance toFiniteModule_additive : (toFiniteModule.{u, v} F).Additive where
  map_add := by intros; rfl

instance fromFiniteModule_additive : (fromFiniteModule.{u, v} F).Additive where
  map_add := by intros; rfl

/-- The actual inclusion is an equivalence, with the identity maps as unit and counit. -/
def finiteModuleEquivalence : Category.{u, v} F ≌ FGModuleCat.{v} F where
  functor := toFiniteModule F
  inverse := fromFiniteModule F
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance toFiniteModule_isEquivalence : (toFiniteModule.{u, v} F).IsEquivalence :=
  (finiteModuleEquivalence F).isEquivalence_functor

/-- The inclusion preserves conflations by their actual projective splitting. -/
def toFiniteModuleExact : ExactFunctor (exactStructure.{u, v} F)
    (ModuleCat.finiteModuleExactStructure.{u, v} F) where
  toFunctor := toFiniteModule F
  map_conflation S hS := ((splittingOfConflation F S hS).map (toFiniteModule F)).shortExact

/-- The inverse preserves the original ambient short exact sequence. -/
def fromFiniteModuleExact : ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, v} F)
    (exactStructure.{u, v} F) where
  toFunctor := fromFiniteModule F
  map_conflation _ hS := hS.map_of_exact (forget₂ (FGModuleCat F) (ModuleCat F))

instance toFiniteModuleExact_mapQ_isEquivalence :
    (toFiniteModuleExact.{u, v} F).mapQ.IsEquivalence := by
  let : (toFiniteModuleExact.{u, v} F).toFunctor.IsEquivalence :=
    toFiniteModule_isEquivalence F
  exact (toFiniteModuleExact F).mapQ_isEquivalence_of_equivalence
    (fun i h => (fromFiniteModuleExact F).map_inflation _ h)
    (fun p h => (fromFiniteModuleExact F).map_deflation _ h)

/-- The finite-module K-equivalence has exactly the inclusion's original K-map forward. -/
def finiteModuleKEquiv (n : ℕ) : (exactStructure.{u, v} F).K n ≃*
    (ModuleCat.finiteModuleExactStructure.{u, v} F).K n :=
  (toFiniteModuleExact F).KEquivOfMapQIsEquivalence n

@[simp]
theorem finiteModuleKEquiv_apply (n : ℕ) (a : (exactStructure.{u, v} F).K n) :
    finiteModuleKEquiv F n a = (toFiniteModuleExact F).KMap n a := rfl

/-- The actual upper-universe finite-module SmallModel comparison. -/
def upperFiniteModuleKEquiv (n : ℕ) : (exactStructure.{u, u} F).K n ≃*
    (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u+1} n :=
  (finiteModuleKEquiv F n).trans
    ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u+1}.commonAmbientKEquiv
      n).symm

/-- The SmallModel component is the inverse of its original common-ambient Q-map. -/
theorem upperFiniteModuleKEquiv_toOriginal (n : ℕ) (a : (exactStructure.{u, u} F).K n) :
    (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u+1}.commonAmbientKMap n
      (upperFiniteModuleKEquiv F n a) = (toFiniteModuleExact F).KMap n a := by
  let E := ModuleCat.finiteModuleExactStructure.{u, u} F
  exact (E.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).apply_symm_apply _

end Quillen.FiniteProjectiveModule
