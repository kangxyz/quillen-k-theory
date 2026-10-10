/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportUnion
public import Quillen.Waldhausen.Functoriality.ExactEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.LongExactSequence

/-!
# The actual bounded-flat supported relative fiber and boundary

The genuine relative acyclic category is identified with original support on
T ∪ range(j), preserving its actual complex, chain maps and inclusion. The
original joint cylinder and extension axiom prove the canonical fiber comparison
weak and define the original connecting map. No compactness premise is used.
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
lemma boundedFlatPerfectSupported_sup_opensRange_iff {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (A : Complex X) :
    boundedFlatPerfectSupported (T ⊔ j.opensRange).ι A ↔
      boundedFlatPerfectSupported T.ι A ∧ ((restrict j).obj A).Acyclic := by
  change (boundedFlatPerfect X A ∧ _) ↔ (boundedFlatPerfect X A ∧ _) ∧ _
  rw [restrictAcyclic_sup_iff, restrictAcyclic_opensRange_iff]
  tauto

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Relative coarse acyclicity is the actual support predicate, in every degree. -/
theorem boundedFlatPerfectSupportedOpenAcyclic_iff (K : (boundedFlatPerfectSupported
  T.ι).FullSubcategory) :
    Acyclic (boundedFlatPerfectSupportedOpenWaldhausen j T) K ↔ ((restrict j).obj K.obj).Acyclic :=
      by
  have hZ : IsZero ((restrict j).obj (boundedFlatPerfectSupportedWaldhausen T.ι).zero.obj) :=
    (restrict j).map_isZero ((boundedFlatPerfectSupported T.ι).ι.map_isZero
      (boundedFlatPerfectSupportedWaldhausen T.ι).isZero)
  change QuasiIso ((restrict j).map ((boundedFlatPerfectSupportedWaldhausen T.ι).isZero.to_ K).hom)
    ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun n ↦ quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)

/-- Forget the redundant nested full-subcategory wrapper. -/
def boundedFlatPerfectSupportedOpenAcyclicToSupported :
    AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T) ⥤ (boundedFlatPerfectSupported (T ⊔
      j.opensRange).ι).FullSubcategory where
  obj K := ⟨K.obj.obj, (boundedFlatPerfectSupported_sup_opensRange_iff j T K.obj.obj).mpr
    ⟨K.obj.property, (boundedFlatPerfectSupportedOpenAcyclic_iff j T K.obj).1 K.property⟩⟩
  map f := (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the genuine relative-acyclic witness from the original support predicate. -/
def boundedFlatPerfectSupportedUnionToAcyclic :
    (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory ⥤ AcyclicCategory
      (boundedFlatPerfectSupportedOpenNested j T) where
  obj K := ⟨⟨K.obj, ((boundedFlatPerfectSupported_sup_opensRange_iff j T K.obj).mp K.property).1⟩,
    (boundedFlatPerfectSupportedOpenAcyclic_iff j T _).2
      ((boundedFlatPerfectSupported_sup_opensRange_iff j T K.obj).mp K.property).2⟩
  map f := (acyclicObjects (boundedFlatPerfectSupportedOpenNested j T)).homMk
    ((boundedFlatPerfectSupported T.ι).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flattening preserves the actual underlying chain complex. -/
@[simp] theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_obj
    (K : AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T)) :
    ((boundedFlatPerfectSupportedOpenAcyclicToSupported j T).obj K).obj = K.obj.obj := rfl

/-- Flattening preserves each actual underlying chain map. -/
@[simp] theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_map
    {K L : AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T)} (f : K ⟶ L) :
    ((boundedFlatPerfectSupportedOpenAcyclicToSupported j T).map f).hom = f.hom.hom := rfl

/-- The inverse preserves the same underlying chain complex. -/
@[simp] theorem boundedFlatPerfectSupportedUnionToAcyclic_obj
    (K : (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :
    ((boundedFlatPerfectSupportedUnionToAcyclic j T).obj K).obj.obj = K.obj := rfl

/-- The inverse preserves the same underlying chain map. -/
@[simp] theorem boundedFlatPerfectSupportedUnionToAcyclic_map
    {K L : (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory} (f : K ⟶ L) :
    ((boundedFlatPerfectSupportedUnionToAcyclic j T).map f).hom.hom = f.hom := rfl

/-- The actual composite is the identity, including its morphism function. -/
@[simp] theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_comp_inverse :
    boundedFlatPerfectSupportedOpenAcyclicToSupported j T ⋙
      boundedFlatPerfectSupportedUnionToAcyclic j T =
      𝟭 (AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T)) := rfl

/-- The actual inverse composite is also the identity functor. -/
@[simp] theorem boundedFlatPerfectSupportedUnionToAcyclic_comp_inverse :
    boundedFlatPerfectSupportedUnionToAcyclic j T ⋙
      boundedFlatPerfectSupportedOpenAcyclicToSupported j T =
      𝟭 ((boundedFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) := rfl

/-- Forgetting support after flattening is the original acyclic inclusion. -/
@[simp] theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_comp_inclusion :
    boundedFlatPerfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show boundedFlatPerfectSupported (T ⊔ j.opensRange).ι ≤ boundedFlatPerfectSupported T.ι from
        fun K h ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) =
      acyclicInclusion (boundedFlatPerfectSupportedOpenNested j T) := rfl

/-- Forgetting relative acyclicity after the inverse is the original inclusion. -/
@[simp] theorem boundedFlatPerfectSupportedUnionToAcyclic_comp_inclusion :
    boundedFlatPerfectSupportedUnionToAcyclic j T ⋙ acyclicInclusion
      (boundedFlatPerfectSupportedOpenNested j T) =
      ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported (T ⊔ j.opensRange).ι ≤ boundedFlatPerfectSupported T.ι
          from fun K h ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) := rfl

/-- The two actual categories are equivalent without any localization assumption. -/
def boundedFlatPerfectSupportedOpenAcyclicSupportedEquivalence :
    AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T) ≌ (boundedFlatPerfectSupported (T ⊔
      j.opensRange).ι).FullSubcategory where
  functor := boundedFlatPerfectSupportedOpenAcyclicToSupported j T
  inverse := boundedFlatPerfectSupportedUnionToAcyclic j T
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (boundedFlatPerfectSupportedOpenAcyclicToSupported j T).IsEquivalence :=
  (boundedFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_functor
local instance : (boundedFlatPerfectSupportedUnionToAcyclic j T).IsEquivalence :=
  (boundedFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).isEquivalence_inverse

/-- A fine cofibration between supported objects has a supported quotient. -/
theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_cofibration
    {A B : AcyclicCategory (boundedFlatPerfectSupportedOpenNested j T)} (f : A ⟶ B)
    (hf : (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).cof f) :
    (boundedFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      ((boundedFlatPerfectSupportedOpenAcyclicToSupported j T).map f) := by
  obtain ⟨Z, hZ, p, hp, hS⟩ :=
    (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
      (boundedFlatPerfectSupported T.ι) f.hom).1 hf
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
    (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι)
      ((boundedFlatPerfectSupportedOpenAcyclicToSupported j T).map f)).2
  refine ⟨Z, (boundedFlatPerfectSupported_sup_opensRange_iff j T Z).mpr ⟨hZ, ?_⟩, p, hp, hS⟩
  have hS' : (ShortComplex.mk f.hom.hom p hp).ShortExact := hS
  apply (hS'.map_of_exact (restrict j)).acyclic_X₃
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    ((boundedFlatPerfectSupportedOpenAcyclic_iff j T A.obj).1 A.property n)).2
    ((boundedFlatPerfectSupportedOpenAcyclic_iff j T B.obj).1 B.property n)

/-- Flattening is exact for the original inherited fine weak equivalences. -/
theorem boundedFlatPerfectSupportedOpenAcyclicToSupported_exact :
    IsExact (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).cof
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).weq
      (boundedFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
        (boundedFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (boundedFlatPerfectSupportedOpenAcyclicToSupported j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectSupportedUnionToAcyclic j T) _ h
  cofibration f h := boundedFlatPerfectSupportedOpenAcyclicToSupported_cofibration j T f h
  weak _ h := h
  pushout _ h := h.map (boundedFlatPerfectSupportedOpenAcyclicToSupported j T)

/-- The inverse functor is exact with precisely the same fine morphism classes. -/
theorem boundedFlatPerfectSupportedUnionToAcyclic_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      (boundedFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).cof
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).weq
      (boundedFlatPerfectSupportedUnionToAcyclic j T) where
  zero h := IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectSupportedOpenAcyclicToSupported
    j T) _ h
  cofibration f h := (subcategoryInclusion_exact (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι)
    (boundedFlatPerfectSupported T.ι) (fun K h ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff j
      T K).mp h).1)).cofibration f h
  weak _ h := h
  pushout _ h := h.map (boundedFlatPerfectSupportedUnionToAcyclic j T)

/-- The actual supported inclusion is preserved at the functor level. -/
def boundedFlatPerfectSupportedOpenAcyclicToSupportedInclusionIso :
    boundedFlatPerfectSupportedOpenAcyclicToSupported j T ⋙ ObjectProperty.ιOfLE
      (show boundedFlatPerfectSupported (T ⊔ j.opensRange).ι ≤ boundedFlatPerfectSupported T.ι from
        fun K h ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) ≅
      acyclicInclusion (boundedFlatPerfectSupportedOpenNested j T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- Forget only the additional acyclicity on the open, retaining the prescribed support. -/
def boundedFlatPerfectSupportedUnionKMap (n : ℕ) :
    BoundedFlatPerfectSupportedK (T ⊔ j.opensRange).ι n →* BoundedFlatPerfectSupportedK T.ι n :=
  subcategoryKMap (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι) (boundedFlatPerfectSupported
    T.ι)
    (fun K h => ((boundedFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1) n

/-- The genuine all-degree K-equivalence of the two original supported models. -/
def boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (boundedFlatPerfectSupportedOpenNested j T)).K n ≃*
      BoundedFlatPerfectSupportedK (T ⊔ j.opensRange).ι n :=
  KEquivOfExactEquivalence _ _ (boundedFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T)
    (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact j T)
      (boundedFlatPerfectSupportedUnionToAcyclic_exact j T) n

/-- Flattening intertwines the original supported inclusion, literally its public K-map. -/
theorem boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (boundedFlatPerfectSupportedUnionKMap j T n).comp
      (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (acyclicInclusion_exact (boundedFlatPerfectSupportedOpenNested j T)) n := by
  change (KMap (subcategoryInclusion_exact (boundedFlatPerfectSupported (T ⊔ j.opensRange).ι)
    (boundedFlatPerfectSupported T.ι)
    (fun K h ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff j T K).mp h).1)) n).comp (KMap
      (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact j T) n) = _
  rw [Quillen.Waldhausen.KMap_comp_KMap]

/-- The inverse K-equivalence identifies the same canonical supported inclusion. -/
theorem boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (boundedFlatPerfectSupportedOpenNested j T)) n).comp
      (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom =
        boundedFlatPerfectSupportedUnionKMap j T n := by
  ext x
  have h := DFunLike.congr_fun (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inclusion j T
    n)
    ((boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm x)
  simpa using h.symm

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

instance instHasTwoOutOfThreePropertyBoundedFlatPerfectSupportedOpenNested :
    (boundedFlatPerfectSupportedOpenNested j T).coarse.weq.HasTwoOutOfThreeProperty := by
  let : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (Waldhausen.subcategoryWeakEquivalences (perfectSupported (j ⁻¹ᵁ
      T).ι)).HasTwoOutOfThreeProperty
  exact Waldhausen.Structure.withInverseImageWeak_twoOutOfThree
    ((boundedFlatPerfectSupportedInclusion_exact T.ι).comp (perfectSupportedRestrict_exact j T))

/-- Exact restriction proves the genuine coarse extension axiom. -/
theorem boundedFlatPerfectSupportedOpenWaldhausen_extensionAxiom :
    ExtensionAxiom (boundedFlatPerfectSupportedOpenWaldhausen j T) :=
  Structure.withInverseImageWeak_extensionAxiom
    ((boundedFlatPerfectSupportedInclusion_exact T.ι).comp (perfectSupportedRestrict_exact j T))
    (complexSubcategory_extensionAxiom (perfectSupported (j ⁻¹ᵁ T).ι))

/-- The actual second cylinder endpoint is a section of its original projection. -/
theorem boundedFlatPerfectSupportedOpenJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (boundedFlatPerfectSupportedOpenNested j T)
      (boundedFlatPerfectSupportedOpenJointData j T) :=
  complexJointDataOfNested_secondEndpointSection (boundedFlatPerfectSupported T.ι)
    (fun hK hL f => boundedFlatPerfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK => boundedFlatPerfectSupported_shift T.ι hK 1) (boundedFlatPerfectSupportedOpenNested
      j T)

/-- The original bounded-flat relative canonical fiber comparison is genuinely weak. -/
theorem boundedFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedFlatPerfectSupportedOpenNested j T)) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedFlatPerfectSupportedOpenNested j T)
    (boundedFlatPerfectSupportedOpenWaldhausen_extensionAxiom j T)
      (boundedFlatPerfectSupportedOpenJointData j T)
    (boundedFlatPerfectSupportedOpenJointData_secondEndpointSection j T)

/-- The genuine original homotopy-fiber boundary with supported bounded-flat target. -/
def boundedFlatPerfectSupportedOpenConnectingHom (n : ℕ) :
    BoundedFlatPerfectSupportedOpenK j T (n+1) →* BoundedFlatPerfectSupportedK (T ⊔ j.opensRange).ι
      n :=
  (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom.comp
    (changeWeakConnectingHom (boundedFlatPerfectSupportedOpenNested j T)
      (boundedFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n)

end Quillen.PerfectComplexes

end
