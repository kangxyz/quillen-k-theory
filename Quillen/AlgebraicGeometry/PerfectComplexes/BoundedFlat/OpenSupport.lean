/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportComparison
public import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-!
# Supported bounded-flat complexes as actual relative acyclics

The original relative-acyclic category is exactly equivalent to the supported
bounded-flat full subcategory. Cofibrations retain their genuine supported
quotients, as proved by exact restriction and its homology sequence.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Relative coarse acyclicity is the actual support predicate, in every degree. -/
theorem boundedFlatPerfectOpenAcyclic_iff (K : BoundedFlatPerfect X) :
    Acyclic (boundedFlatPerfectOpenWaldhausen j) K ↔ ((restrict j).obj K.obj).Acyclic := by
  have hZ : IsZero ((restrict j).obj (boundedFlatPerfectWaldhausen X).zero.obj) :=
    (restrict j).map_isZero ((boundedFlatPerfect X).ι.map_isZero (boundedFlatPerfectWaldhausen
      X).isZero)
  change QuasiIso ((restrict j).map ((boundedFlatPerfectWaldhausen X).isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def boundedFlatPerfectAcyclicToSupported :
    AcyclicCategory (boundedFlatPerfectOpenNested j) ⥤ (boundedFlatPerfectSupported
      j).FullSubcategory where
  obj K := ⟨K.obj.obj, K.obj.property, (boundedFlatPerfectOpenAcyclic_iff j K.obj).1 K.property⟩
  map f := (boundedFlatPerfectSupported j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def boundedFlatPerfectSupportedToAcyclic :
    (boundedFlatPerfectSupported j).FullSubcategory ⥤ AcyclicCategory (boundedFlatPerfectOpenNested
      j) where
  obj K := ⟨⟨K.obj, K.property.1⟩,
    (boundedFlatPerfectOpenAcyclic_iff j ⟨K.obj, K.property.1⟩).2 K.property.2⟩
  map f := (acyclicObjects (boundedFlatPerfectOpenNested j)).homMk ((boundedFlatPerfect X).homMk
    f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem boundedFlatPerfectAcyclicToSupported_obj
    (K : AcyclicCategory (boundedFlatPerfectOpenNested j)) :
    ((boundedFlatPerfectAcyclicToSupported j).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem boundedFlatPerfectAcyclicToSupported_map
    {K L : AcyclicCategory (boundedFlatPerfectOpenNested j)} (f : K ⟶ L) :
    ((boundedFlatPerfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem boundedFlatPerfectSupportedToAcyclic_obj
    (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    ((boundedFlatPerfectSupportedToAcyclic j).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem boundedFlatPerfectSupportedToAcyclic_map
    {K L : (boundedFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    ((boundedFlatPerfectSupportedToAcyclic j).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem boundedFlatPerfectAcyclicToSupported_comp_inverse :
    boundedFlatPerfectAcyclicToSupported j ⋙ boundedFlatPerfectSupportedToAcyclic j =
      𝟭 (AcyclicCategory (boundedFlatPerfectOpenNested j)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem boundedFlatPerfectSupportedToAcyclic_comp_inverse :
    boundedFlatPerfectSupportedToAcyclic j ⋙ boundedFlatPerfectAcyclicToSupported j =
      𝟭 ((boundedFlatPerfectSupported j).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem boundedFlatPerfectAcyclicToSupported_comp_inclusion :
    boundedFlatPerfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect X from fun _ h ↦ h.1) =
      acyclicInclusion (boundedFlatPerfectOpenNested j) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem boundedFlatPerfectSupportedToAcyclic_comp_inclusion :
    boundedFlatPerfectSupportedToAcyclic j ⋙ acyclicInclusion (boundedFlatPerfectOpenNested j) =
      ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect X from fun _ h ↦ h.1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def boundedFlatPerfectAcyclicSupportedEquivalence :
    AcyclicCategory (boundedFlatPerfectOpenNested j) ≌ (boundedFlatPerfectSupported
      j).FullSubcategory where
  functor := boundedFlatPerfectAcyclicToSupported j
  inverse := boundedFlatPerfectSupportedToAcyclic j
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (boundedFlatPerfectAcyclicToSupported j).IsEquivalence :=
  (boundedFlatPerfectAcyclicSupportedEquivalence j).isEquivalence_functor
local instance : (boundedFlatPerfectSupportedToAcyclic j).IsEquivalence :=
  (boundedFlatPerfectAcyclicSupportedEquivalence j).isEquivalence_inverse

/-- A fine cofibration between supported objects has a supported quotient. -/
theorem boundedFlatPerfectAcyclicToSupported_cofibration
    {A B : AcyclicCategory (boundedFlatPerfectOpenNested j)} (f : A ⟶ B)
    (hf : (acyclicStructure (boundedFlatPerfectOpenNested j)).cof f) :
    (boundedFlatPerfectSupportedWaldhausen j).cof ((boundedFlatPerfectAcyclicToSupported j).map f)
      := by
  obtain ⟨Z, hZ, p, hp, hS⟩ :=
    (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
      (boundedFlatPerfect X) f.hom).1 hf
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
    (boundedFlatPerfectSupported j) ((boundedFlatPerfectAcyclicToSupported j).map f)).2
  refine ⟨Z, ⟨hZ, ?_⟩, p, hp, hS⟩
  have hS' : (ShortComplex.mk f.hom.hom p hp).ShortExact := hS
  apply (hS'.map_of_exact (restrict j)).acyclic_X₃
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    ((boundedFlatPerfectOpenAcyclic_iff j A.obj).1 A.property n)).2
    ((boundedFlatPerfectOpenAcyclic_iff j B.obj).1 B.property n)

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem boundedFlatPerfectAcyclicToSupported_exact :
    IsExact (acyclicStructure (boundedFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatPerfectAcyclicToSupported j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectSupportedToAcyclic j) _ h
  cofibration f h := boundedFlatPerfectAcyclicToSupported_cofibration j f h
  weak _ h := h
  pushout _ h := h.map (boundedFlatPerfectAcyclicToSupported j)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem boundedFlatPerfectSupportedToAcyclic_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).cof (boundedFlatPerfectSupportedWaldhausen
      j).weq
      (acyclicStructure (boundedFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).weq
      (boundedFlatPerfectSupportedToAcyclic j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectAcyclicToSupported j) _ h
  cofibration f h := (subcategoryInclusion_exact (boundedFlatPerfectSupported j)
    (boundedFlatPerfect X) (fun _ h ↦ h.1)).cofibration f h
  weak _ h := h
  pushout _ h := h.map (boundedFlatPerfectSupportedToAcyclic j)

/-- The actual supported inclusion is preserved at the functor level. -/
def boundedFlatPerfectAcyclicToSupportedInclusionIso :
    boundedFlatPerfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect X from fun _ h ↦ h.1) ≅
      acyclicInclusion (boundedFlatPerfectOpenNested j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The genuine all-degree K-equivalence of the two original supported models. -/
def boundedFlatPerfectAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (boundedFlatPerfectOpenNested j)).K n ≃* BoundedFlatPerfectSupportedK j n :=
  KEquivOfExactEquivalence _ _ (boundedFlatPerfectAcyclicSupportedEquivalence j)
    (boundedFlatPerfectAcyclicToSupported_exact j) (boundedFlatPerfectSupportedToAcyclic_exact j) n

/-- Flattening intertwines the original supported inclusion, literally its public K-map. -/
theorem boundedFlatPerfectAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (boundedFlatPerfectSupportedKMap j n).comp (boundedFlatPerfectAcyclicSupportedKEquiv j
      n).toMonoidHom =
      KMap (acyclicInclusion_exact (boundedFlatPerfectOpenNested j)) n := by
  change (KMap (subcategoryInclusion_exact (boundedFlatPerfectSupported j) (boundedFlatPerfect X)
    (fun _ h ↦ h.1)) n).comp (KMap (boundedFlatPerfectAcyclicToSupported_exact j) n) = _
  rw [Quillen.Waldhausen.KMap_comp_KMap]

/-- The inverse K-equivalence identifies the same canonical supported inclusion. -/
theorem boundedFlatPerfectAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (boundedFlatPerfectOpenNested j)) n).comp
      (boundedFlatPerfectAcyclicSupportedKEquiv j n).symm.toMonoidHom =
        boundedFlatPerfectSupportedKMap j n := by
  ext x
  have h := DFunLike.congr_fun (boundedFlatPerfectAcyclicSupportedKEquiv_inclusion j n)
    ((boundedFlatPerfectAcyclicSupportedKEquiv j n).symm x)
  simpa using h.symm

end Quillen.PerfectComplexes
