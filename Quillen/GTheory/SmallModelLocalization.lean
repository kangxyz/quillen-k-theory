/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Localization.SmallModel
public import Quillen.Localization.Serre.LocalizationTarget

/-!
# Canonical connective localization on actual small exact models

An actual exact functor between essentially small abelian categories which is
a Serre localization yields the connective localization sequence for its original
`smallKMap`. All categorical quotient and exact-structure comparisons are proved;
the only localization hypothesis here concerns the actual input functor.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SmallModelGLocalization
private theorem exact_transport
    {A B C A' B' C' : Type w}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The actual Serre kernel in the chosen source small model. -/
abbrev supported : ObjectProperty (SmallModel.{w} C) :=
  (SmallModelLocalization.functor F.toFunctor).kernel

/-- The genuine supported K-term in the chosen small model. -/
abbrev SupportedK (n : ℕ) := (CategoryTheory.ObjectProperty.subcategoryExactStructure (supported
  F)).K n

/-- The canonical inclusion, followed by the identity exact-structure comparison. -/
def inclusionKMap (n : ℕ) : SupportedK F n →* (abelianExactStructure C).SmallK n :=
  (SmallModelLocalization.standardKEquiv C n).symm.toMonoidHom.comp
    (Devissage.KMap (supported F) n)

/-- The boundary from the actual target, with the canonical small exact-structure comparison. -/
def connectingHom (n : ℕ) : (abelianExactStructure D).SmallK (n + 1) →* SupportedK F n :=
  (SerreLocalization.actualConnectingHom (supported F)
    (SmallModelLocalization.functor F.toFunctor) n).comp
      (SmallModelLocalization.standardKEquiv D (n + 1)).toMonoidHom

lemma KMap_comparison (n : ℕ) (x : (abelianExactStructure C).SmallK n) :
    SmallModelLocalization.standardKEquiv D n (F.smallKMap n x) =
      SerreLocalization.KMap (supported F) (SmallModelLocalization.functor F.toFunctor) n
        (SmallModelLocalization.standardKEquiv C n x) := by
  exact DFunLike.congr_fun (SmallModelLocalization.smallKMap_comparison F n) x

/-- Exactness at the original canonical small-model K-group of C. -/
theorem inclusion_range_eq_KMap_ker (n : ℕ) :
    (inclusionKMap F n).range = (F.smallKMap n).ker := by
  apply exact_transport (inclusionKMap F n) (F.smallKMap n)
    (Devissage.KMap (supported F) n)
    (SerreLocalization.KMap (supported F) (SmallModelLocalization.functor F.toFunctor) n)
    (MulEquiv.refl _) (SmallModelLocalization.standardKEquiv C n)
    (SmallModelLocalization.standardKEquiv D n)
  · intro a
    exact (SmallModelLocalization.standardKEquiv C n).apply_symm_apply _
  · exact KMap_comparison F n
  · exact SerreLocalization.actual_inclusion_range_eq_KMap_ker _ _ n

/-- Exactness at the original canonical small-model K-group of D. -/
theorem KMap_range_eq_connecting_ker (n : ℕ) :
    (F.smallKMap (n + 1)).range = (connectingHom F n).ker := by
  apply exact_transport (F.smallKMap (n + 1)) (connectingHom F n)
    (SerreLocalization.KMap (supported F) (SmallModelLocalization.functor F.toFunctor) (n + 1))
    (SerreLocalization.actualConnectingHom (supported F)
      (SmallModelLocalization.functor F.toFunctor) n)
    (SmallModelLocalization.standardKEquiv C (n + 1))
    (SmallModelLocalization.standardKEquiv D (n + 1)) (MulEquiv.refl _)
  · exact KMap_comparison F (n + 1)
  · intro a; rfl
  · exact SerreLocalization.actual_KMap_range_eq_connecting_ker _ _ n

/-- Exactness at the actual small-model supported K-term. -/
theorem connecting_range_eq_inclusion_ker (n : ℕ) :
    (connectingHom F n).range = (inclusionKMap F n).ker := by
  apply exact_transport (connectingHom F n) (inclusionKMap F n)
    (SerreLocalization.actualConnectingHom (supported F)
      (SmallModelLocalization.functor F.toFunctor) n)
    (Devissage.KMap (supported F) n)
    (SmallModelLocalization.standardKEquiv D (n + 1)) (MulEquiv.refl _)
    (SmallModelLocalization.standardKEquiv C n)
  · intro a; rfl
  · intro a
    exact (SmallModelLocalization.standardKEquiv C n).apply_symm_apply _
  · exact SerreLocalization.actual_connecting_range_eq_inclusion_ker _ _ n

/-- The original canonical small-model K₀ map is surjective. -/
theorem KZero_surjective : Function.Surjective (F.smallKMap 0) := by
  intro y
  obtain ⟨x, hx⟩ := SerreLocalization.actualKZero_surjective (supported F)
    (SmallModelLocalization.functor F.toFunctor) (SmallModelLocalization.standardKEquiv D 0 y)
  refine ⟨(SmallModelLocalization.standardKEquiv C 0).symm x,
    (SmallModelLocalization.standardKEquiv D 0).injective ?_⟩
  rw [KMap_comparison, MulEquiv.apply_symm_apply, hx]

/-- The complete canonical connective localization sequence on actual small models. -/
theorem localization_longExact :
    (∀ n, (inclusionKMap F n).range = (F.smallKMap n).ker) ∧
    (∀ n, (F.smallKMap (n + 1)).range = (connectingHom F n).ker) ∧
    (∀ n, (connectingHom F n).range = (inclusionKMap F n).ker) ∧
    Function.Surjective (F.smallKMap 0) :=
  ⟨inclusion_range_eq_KMap_ker F, KMap_range_eq_connecting_ker F,
    connecting_range_eq_inclusion_ker F, KZero_surjective F⟩

end Quillen.SmallModelGLocalization
