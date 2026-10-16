/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Exact
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.Algebra.Category.FGModuleCat.Localization.Quotient
public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Actual finite-module localization on small models

This file retains the canonical exact localization functor while transporting
its genuine Serre quotient theorem to the chosen small module categories.
The comparison with principal-open sheaf restriction is a separate theorem.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open ModuleCat.FiniteLocalization


open ModuleCat


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- The actual finite-module localization, as an exact functor. -/
def exactFunctor : ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} R)
    (ModuleCat.finiteModuleExactStructure.{u, u} (Localization S)) where
  toFunctor := functor S
  map_conflation _ h := h.map_of_exact _

/-- The canonical small-model functor, using the same choices as `smallKMap`. -/
abbrev smallFunctor : SmallModel.{u} (FGModuleCat.{u} R) ⥤
    SmallModel.{u} (FGModuleCat.{u} (Localization S)) :=
  (exactFunctor S).smallModel.toFunctor

instance smallFunctor_preservesFiniteLimits : PreservesFiniteLimits (smallFunctor S) := by
  change PreservesFiniteLimits (((equivSmallModel (FGModuleCat R)).inverse ⋙ functor S) ⋙
    (equivSmallModel (FGModuleCat (Localization S))).functor)
  infer_instance

instance smallFunctor_preservesFiniteColimits : PreservesFiniteColimits (smallFunctor S) := by
  change PreservesFiniteColimits (((equivSmallModel (FGModuleCat R)).inverse ⋙ functor S) ⋙
    (equivSmallModel (FGModuleCat (Localization S))).functor)
  infer_instance

/-- The actual Serre kernel of finite-module localization on the small model. -/
def smallTorsion : ObjectProperty (SmallModel.{u} (FGModuleCat.{u} R)) :=
  (smallFunctor S).kernel

instance smallTorsion_isSerreClass : (smallTorsion S).IsSerreClass := by
  dsimp [smallTorsion]
  infer_instance

/-- The source equivalence commutes with actual localization, with its canonical
unit comparison. -/
def smallFunctorComparison :
    (equivSmallModel (FGModuleCat.{u} R)).functor ⋙ smallFunctor S ≅
      functor S ⋙ (equivSmallModel (FGModuleCat.{u} (Localization S))).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (equivSmallModel (FGModuleCat.{u} R)).unitIso.symm _ ≪≫
      Functor.leftUnitor _) _

/-- The quotient theorem survives the genuine small-model transport. -/
instance smallFunctor_isLocalization :
    (smallFunctor S).IsLocalization (smallTorsion S).isoModSerre := by
  let L := functor S ⋙ (equivSmallModel (FGModuleCat.{u} (Localization S))).functor
  have hinv : (smallTorsion S).isoModSerre.IsInvertedBy (smallFunctor S) := by
    change (smallFunctor S).kernel.isoModSerre.IsInvertedBy (smallFunctor S)
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro X Y f hf
    exact hf
  apply Functor.IsLocalization.of_equivalence_source L (torsion S).isoModSerre
    (smallFunctor S) (smallTorsion S).isoModSerre (equivSmallModel (FGModuleCat R))
    ?_ hinv (smallFunctorComparison S)
  have hi : (torsion S).isoModSerre.IsInvertedBy
      ((equivSmallModel (FGModuleCat R)).functor ⋙ smallFunctor S) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (smallFunctorComparison S)).2
      (Localization.inverts L (torsion S).isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  change (smallFunctor S).kernel.isoModSerre _
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Small-model torsion means torsion of the actual finite module represented. -/
theorem smallTorsion_iff (M : SmallModel.{u} (FGModuleCat.{u} R)) :
    smallTorsion S M ↔ torsion S ((equivSmallModel (FGModuleCat R)).inverse.obj M) := by
  change IsZero ((equivSmallModel (FGModuleCat (Localization S))).functor.obj
      ((functor S).obj ((equivSmallModel (FGModuleCat R)).inverse.obj M))) ↔
    IsZero ((functor S).obj ((equivSmallModel (FGModuleCat R)).inverse.obj M))
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero _ _ h, fun h ↦ Functor.map_isZero _ h⟩

/-- The same small functor, equipped with the standard abelian exact structures. -/
def smallAbelianExactFunctor :
    ExactFunctor (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R)))
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (Localization S)))) where
  toFunctor := smallFunctor S
  map_conflation _ h := h.map_of_exact _

/-- The identity comparison from the transported small exact structure to
its equal standard abelian exact structure. -/
def smallModelToAbelian (A : Type u) [CommRing A] [IsNoetherianRing A] :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} A).smallModel
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} A))) where
  toFunctor := 𝟭 _
  map_conflation _ h := by
    change ((abelianExactStructure (FGModuleCat.{u} A)).smallModel).conflation _ at h
    rw [abelianExactStructure_smallModel] at h
    exact h

instance smallModelToAbelian_isEquivalence (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (smallModelToAbelian A).toFunctor.IsEquivalence := inferInstanceAs (𝟭 _).IsEquivalence

/-- The supported small-model objects for a principal open are exactly
represented finite modules annihilated by one power of its defining element. -/
theorem smallTorsion_powers_iff_uniform (f : R)
    (M : SmallModel.{u} (FGModuleCat.{u} R)) :
    smallTorsion (Submonoid.powers f) M ↔ ∃ n : ℕ,
      ∀ m : (equivSmallModel (FGModuleCat R)).inverse.obj M, f ^ n • m = 0 := by
  rw [smallTorsion_iff, torsion_powers_iff_uniform]

end Quillen.FiniteModuleLocalization
