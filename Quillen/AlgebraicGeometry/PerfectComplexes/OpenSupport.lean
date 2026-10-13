/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFibration
public import Quillen.AlgebraicGeometry.PerfectComplexes.PerfectSupport
public import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-!
# Supported perfect complexes as the actual relative-acyclic category

The relative-acyclic category and the existing supported full subcategory are
identified by actual, mutually inverse exact functors. The nontrivial
cofibration comparison uses the long exact homology sequence after restriction.
The K-equivalence retains the existing supported inclusion homomorphism.
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
theorem perfectOpenAcyclic_iff (K : Perfect X) :
    Acyclic (perfectOpenWeakWaldhausen j) K ↔ ((restrict j).obj K.obj).Acyclic := by
  have hZ : IsZero ((restrict j).obj (perfectWaldhausen X).zero.obj) :=
    (restrict j).map_isZero ((locallyPerfect X).ι.map_isZero (perfectWaldhausen X).isZero)
  change QuasiIso ((restrict j).map ((perfectWaldhausen X).isZero.to_ K).hom) ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def perfectAcyclicToSupported :
    AcyclicCategory (perfectOpenNested j) ⥤ (perfectSupported j).FullSubcategory where
  obj K := ⟨K.obj.obj, K.obj.property, (perfectOpenAcyclic_iff j K.obj).1 K.property⟩
  map f := (perfectSupported j).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def perfectSupportedToAcyclic :
    (perfectSupported j).FullSubcategory ⥤ AcyclicCategory (perfectOpenNested j) where
  obj K := ⟨⟨K.obj, K.property.1⟩,
    (perfectOpenAcyclic_iff j ⟨K.obj, K.property.1⟩).2 K.property.2⟩
  map f := (acyclicObjects (perfectOpenNested j)).homMk ((locallyPerfect X).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem perfectAcyclicToSupported_obj
    (K : AcyclicCategory (perfectOpenNested j)) :
    ((perfectAcyclicToSupported j).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem perfectAcyclicToSupported_map
    {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    ((perfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem perfectSupportedToAcyclic_obj
    (K : (perfectSupported j).FullSubcategory) :
    ((perfectSupportedToAcyclic j).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem perfectSupportedToAcyclic_map
    {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    ((perfectSupportedToAcyclic j).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem perfectAcyclicToSupported_comp_inverse :
    perfectAcyclicToSupported j ⋙ perfectSupportedToAcyclic j =
      𝟭 (AcyclicCategory (perfectOpenNested j)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem perfectSupportedToAcyclic_comp_inverse :
    perfectSupportedToAcyclic j ⋙ perfectAcyclicToSupported j =
      𝟭 ((perfectSupported j).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem perfectAcyclicToSupported_comp_inclusion :
    perfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show perfectSupported j ≤ locallyPerfect X from fun _ h ↦ h.1) =
      acyclicInclusion (perfectOpenNested j) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem perfectSupportedToAcyclic_comp_inclusion :
    perfectSupportedToAcyclic j ⋙ acyclicInclusion (perfectOpenNested j) =
      ObjectProperty.ιOfLE
        (show perfectSupported j ≤ locallyPerfect X from fun _ h ↦ h.1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def perfectAcyclicSupportedEquivalence :
    AcyclicCategory (perfectOpenNested j) ≌ (perfectSupported j).FullSubcategory where
  functor := perfectAcyclicToSupported j
  inverse := perfectSupportedToAcyclic j
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (perfectAcyclicToSupported j).IsEquivalence :=
  (perfectAcyclicSupportedEquivalence j).isEquivalence_functor
local instance : (perfectSupportedToAcyclic j).IsEquivalence :=
  (perfectAcyclicSupportedEquivalence j).isEquivalence_inverse

/-- A fine cofibration between supported objects has a supported quotient. -/
theorem perfectAcyclicToSupported_cofibration
    {A B : AcyclicCategory (perfectOpenNested j)} (f : A ⟶ B)
    (hf : (acyclicStructure (perfectOpenNested j)).cof f) :
    (perfectSupportedWaldhausen j).cof ((perfectAcyclicToSupported j).map f) := by
  obtain ⟨Z, hZ, p, hp, hS⟩ :=
    (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
      (locallyPerfect X) f.hom).1 hf
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
    (perfectSupported j) ((perfectAcyclicToSupported j).map f)).2
  refine ⟨Z, ⟨hZ, ?_⟩, p, hp, hS⟩
  have hS' : (ShortComplex.mk f.hom.hom p hp).ShortExact := hS
  apply (hS'.map_of_exact (restrict j)).acyclic_X₃
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    ((perfectOpenAcyclic_iff j A.obj).1 A.property n)).2
    ((perfectOpenAcyclic_iff j B.obj).1 B.property n)

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem perfectAcyclicToSupported_exact :
    IsExact (acyclicStructure (perfectOpenNested j)).cof
      (acyclicStructure (perfectOpenNested j)).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectAcyclicToSupported j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectSupportedToAcyclic j) _ h
  cofibration f h := perfectAcyclicToSupported_cofibration j f h
  weak _ h := h
  pushout _ h := h.map (perfectAcyclicToSupported j)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem perfectSupportedToAcyclic_exact :
    IsExact (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (acyclicStructure (perfectOpenNested j)).cof
      (acyclicStructure (perfectOpenNested j)).weq
      (perfectSupportedToAcyclic j) where
  zero h := IsZero.of_full_of_faithful_of_isZero (perfectAcyclicToSupported j) _ h
  cofibration f h := (subcategoryInclusion_exact (perfectSupported j)
    (locallyPerfect X) (fun _ h ↦ h.1)).cofibration f h
  weak _ h := h
  pushout _ h := h.map (perfectSupportedToAcyclic j)

/-- The actual supported inclusion is preserved at the functor level. -/
def perfectAcyclicToSupportedInclusionIso :
    perfectAcyclicToSupported j ⋙ ObjectProperty.ιOfLE
      (show perfectSupported j ≤ locallyPerfect X from fun _ h ↦ h.1) ≅
      acyclicInclusion (perfectOpenNested j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The genuine all-degree K-equivalence of the two original supported models. -/
def perfectAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (perfectOpenNested j)).K n ≃* PerfectSupportedK j n :=
  KEquivOfExactEquivalence _ _ (perfectAcyclicSupportedEquivalence j)
    (perfectAcyclicToSupported_exact j) (perfectSupportedToAcyclic_exact j) n

/-- Flattening intertwines the original supported inclusion, literally its public K-map. -/
theorem perfectAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (perfectSupportedKMap j n).comp (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectOpenNested j)) n := by
  change (KMap (subcategoryInclusion_exact (perfectSupported j) (locallyPerfect X)
    (fun _ h ↦ h.1)) n).comp (KMap (perfectAcyclicToSupported_exact j) n) = _
  rw [Quillen.Waldhausen.KMap_comp_KMap]

/-- The inverse K-equivalence identifies the same canonical supported inclusion. -/
theorem perfectAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (perfectOpenNested j)) n).comp
      (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom = perfectSupportedKMap j n := by
  ext x
  have h := DFunLike.congr_fun (perfectAcyclicSupportedKEquiv_inclusion j n)
    ((perfectAcyclicSupportedKEquiv j n).symm x)
  simpa using h.symm

end Quillen.PerfectComplexes
