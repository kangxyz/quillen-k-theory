/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Support.FiniteClosedFamilies
public import Quillen.Aglib.CategoryTheory.Pi.Equivalence
public import Quillen.KTheory.FiniteSupport.Decomposition
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralDevissage
public import Quillen.KTheory.Map.NaturalIso

/-!
# Original closed-point pushforward assembly in coherent G-theory

Let `X` be Noetherian and let an injective indexed family of closed points be
presented by actual closed immersions from spectra of the specified fields.
`fieldAssemblyKEquiv` identifies the direct sum of the original public scheme
G-groups in every positive degree with the original upper-small coherent
subcategory on represented sheaf support in that point range. The target
remains a full subcategory of the original ambient small coherent model.

Canonical finite-family reconstruction is transported through actual large
categories inside exact functors with matching upper-small endpoints. The
point categories use `SmallModel.{u+1}` of the actual singleton-supported
coherent categories, and Q2 is applied in that same universe. Native geometric
closed-support dévissage gives each field-coordinate K-equivalence. No
categorical identification with residue vector spaces or comparison of K-groups
across universes is used.

`fieldAssemblyKEquiv_of` retains the original supported lift of closed
pushforward on every singleton. `fieldSupportExactFunctor_comp_ambient` is the
literal ambient exact-functor square; `supportInclusionKMap_comp_assembly`
identifies the ambient composite with the sum of the original public
`coherentPushforwardGMap` maps, including standard exact-structure and zero
normalizations. Explicit K1 and K2 specializations are included.

The native support predicate is ordinary stalk support of the represented
sheaf. Comparison with a separate consumer's stalk-pullback predicate uses its
proved support characterization downstream; no definitional equality with such
a predicate is asserted here. The given closed field immersions are retained,
without replacing their fields by separately chosen scheme residue fields.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ZeroObject DirectSum
attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.FinitePointAssembly

variable (X : Scheme.{u}) [IsNoetherian X] {I : Type u}
  (point : I → X) (closed : ∀ i, IsClosed ({point i} : Set X))

/-- The original upper-small coherent model used in public scheme G-theory. -/
abbrev AmbientCategory := SmallModel.{u+1} (FiniteTypeSheaves X)

/-- Represented ordinary sheaf support contained in the specified geometric point range. -/
def supportProperty : ObjectProperty (AmbientCategory X) := fun M =>
  support ((equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse.obj M).obj ⊆ Set.range point

include closed in
/-- Noetherian closed-point finiteness identifies the actual inverse-image predicate. -/
theorem supportProperty_inverseImage :
    (FiniteClosedFamilies.finitePointSupport X point).inverseImage
      (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse = supportProperty X point := by
  funext M
  exact propext (FiniteClosedFamilies.finitePointSupport_iff_support_subset X point closed _)

instance supportProperty_serre : (supportProperty X point).IsSerreClass where
  exists_zero := by
    let F := (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse ⋙ finiteTypeSheavesToModules X
    have h0 : support (F.obj 0) = ∅ := (support_eq_empty_iff _).2 (F.map_isZero (isZero_zero _))
    refine ⟨0, isZero_zero _, ?_⟩
    change support (F.obj 0) ⊆ Set.range point
    rw [h0]
    exact Set.empty_subset _
  prop_of_mono f hf h := by
    let := hf
    let F := (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse ⋙ finiteTypeSheavesToModules X
    exact (FiniteClosedFamilies.support_subset_of_mono (F.map f)).trans h
  prop_of_epi f hf h := by
    let := hf
    let F := (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse ⋙ finiteTypeSheavesToModules X
    exact (FiniteClosedFamilies.support_subset_of_epi (F.map f)).trans h
  prop_X₂_of_shortExact h h1 h3 := by
    let F := (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse ⋙ finiteTypeSheavesToModules X
    exact (FiniteClosedFamilies.support_middle_subset_union (h.map_of_exact F)).trans
      (Set.union_subset h1 h3)

/-- The actual full supported subcategory of the original upper-small coherent model. -/
abbrev SupportCategory := (supportProperty X point).FullSubcategory
/-- The standard abelian exact structure on the actual supported small category. -/
abbrev supportExactStructure := ObjectProperty.subcategoryExactStructure (supportProperty X point)
/-- Original K-groups of the actual upper-small geometric support subcategory. -/
abbrev SupportK (n : ℕ) := (supportExactStructure X point).K n

/-- Canonical realization compares actual small support with actual finite geometric support. -/
def supportToOriginalEquivalence : SupportCategory X point ≌
    FiniteClosedFamilies.FinitePointSupportCategory X point :=
  (equivSmallModel.{u+1} (FiniteTypeSheaves X)).symm.congrFullSubcategory
    (supportProperty_inverseImage X point closed)

instance supportToOriginal_additive : (supportToOriginalEquivalence X point closed).functor.Additive
    where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse.map_add

/-- Canonical realization of the actual supported model is exact. -/
def supportToOriginalExactFunctor : ExactFunctor (supportExactStructure X point)
    (ObjectProperty.subcategoryExactStructure (FiniteClosedFamilies.finitePointSupport X point))
    where
  toFunctor := (supportToOriginalEquivalence X point closed).functor
  map_conflation _ h := h.map_of_exact _

/-- The inverse supported comparison uses the original ambient small-model functor. -/
def originalToSupportExactFunctor : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (FiniteClosedFamilies.finitePointSupport X point))
    (supportExactStructure X point) where
  toFunctor := (supportToOriginalEquivalence X point closed).inverse
  additive := (supportToOriginalEquivalence X point closed).inverse_additive
  map_conflation _ h := h.map_of_exact _

/-- The actual coherent singleton-supported category, before choosing its small model. -/
abbrev PointOriginal (i : I) := FiniteClosedFamilies.PointCategory X point closed i

instance pointOriginal_essentiallySmall (i : I) :
    EssentiallySmall.{u+1} (PointOriginal X point closed i) :=
  essentiallySmall_of_fully_faithful
    (FiniteClosedSupport.closedSupportProperty X {point i} (closed i)).ι

/-- The canonical upper-small model of actual singleton-supported coherent sheaves. -/
abbrev PointCategory (i : I) := SmallModel.{u+1} (PointOriginal X point closed i)
/-- The standard abelian exact structure on the canonical upper-small point model. -/
abbrev pointExactStructure (i : I) := abelianExactStructure (PointCategory X point closed i)
/-- Original K-groups of the canonical upper-small point category. -/
abbrev PointK (i : I) (n : ℕ) := (pointExactStructure X point closed i).K n

/-- Exact realization of the canonical point model in the actual singleton category. -/
def pointRealizationExactFunctor (i : I) : ExactFunctor (pointExactStructure X point closed i)
    (abelianExactStructure (PointOriginal X point closed i)) where
  toFunctor := (equivSmallModel.{u+1} (PointOriginal X point closed i)).inverse
  map_conflation _ h := h.map_of_exact _

/-- The actual canonical point-model functor is exact. -/
def pointModelExactFunctor (i : I) : ExactFunctor
    (abelianExactStructure (PointOriginal X point closed i)) (pointExactStructure X point closed i)
    where
  toFunctor := (equivSmallModel.{u+1} (PointOriginal X point closed i)).functor
  map_conflation _ h := h.map_of_exact _

/-- The original point inclusion transported as one functor between matching small endpoints. -/
def pointInclusionExactFunctor (i : I) : ExactFunctor (pointExactStructure X point closed i)
    (supportExactStructure X point) :=
  ((pointRealizationExactFunctor X point closed i).comp
    (FiniteClosedFamilies.pointInclusionExactFunctor X point closed i)).comp
      (originalToSupportExactFunctor X point closed)

/-- Actual finite-family reconstruction at the same original upper-small support endpoint. -/
def reconstructionEquivalence (injective : Function.Injective point) :
    Pi.FiniteCategoryFamily (PointCategory X point closed) ≌ SupportCategory X point :=
  (Pi.finiteFamilySmallModelEquivalence.{u, u+1, u, u+1}
    (PointOriginal X point closed)).symm.trans
    ((FiniteClosedFamilies.reconstructionEquivalence X point closed injective).trans
      (supportToOriginalEquivalence X point closed).symm)

/-- One exact reconstruction functor, with large categories only as internal intermediates. -/
def reconstructionExactFunctor (injective : Function.Injective point) : ExactFunctor
    (Pi.finiteCategoryExactStructure (PointCategory X point closed))
    (supportExactStructure X point) :=
  ((Pi.finiteFamilyFromSmallModelExactFunctor.{u, u+1, u, u+1}
    (PointOriginal X point closed)).comp
    (FiniteClosedFamilies.reconstructionExactFunctor X point closed injective)).comp
      (originalToSupportExactFunctor X point closed)

instance reconstructionExactFunctor_isEquivalence (injective : Function.Injective point) :
    (reconstructionExactFunctor X point closed injective).toFunctor.IsEquivalence :=
  (reconstructionEquivalence X point closed injective).isEquivalence_functor

instance reconstructionExactFunctor_mapQ_isEquivalence (injective : Function.Injective point) :
    (reconstructionExactFunctor X point closed injective).mapQ.IsEquivalence := by
  apply (reconstructionExactFunctor X point closed injective).mapQ_isEquivalence_of_equivalence
  · intro A B f hf
    exact (abelianExactStructure_inflation_iff _ f).2
      ((reconstructionExactFunctor X point closed injective).toFunctor.mono_of_mono_map
        ((supportExactStructure X point).mono_of_inflation hf))
  · intro A B f hf
    exact (abelianExactStructure_deflation_iff _ f).2
      ((reconstructionExactFunctor X point closed injective).toFunctor.epi_of_epi_map
        ((supportExactStructure X point).epi_of_deflation hf))

/-- The original upper-small reconstruction K-map is a genuine all-degree equivalence. -/
def reconstructionKEquiv (injective : Function.Injective point) (n : ℕ) :
    (Pi.finiteCategoryExactStructure (PointCategory X point closed)).K n ≃*
      SupportK X point n :=
  (reconstructionExactFunctor X point closed injective).KEquivOfMapQIsEquivalence n

/-- Canonical singleton reconstruction retains the original small point inclusion. -/
def singletonReconstructionIso (injective : Function.Injective point) (i : I) :
    ((Pi.singletonExactInclusion (PointCategory X point closed) i).comp
      (reconstructionExactFunctor X point closed injective)).toFunctor ≅
        (pointInclusionExactFunctor X point closed i).toFunctor := by
  let e := fun i => (equivSmallModel.{u+1} (PointOriginal X point closed i)).symm
  let G := (FiniteClosedFamilies.reconstruction X point closed) ⋙
    (supportToOriginalEquivalence X point closed).inverse
  change Pi.singletonInclusion (PointCategory X point closed) i ⋙
      (Pi.finiteCategoryFamilyEquivalence e).functor ⋙ G ≅ _
  exact Functor.isoWhiskerRight (Pi.finiteCategoryFamilySingletonIso e i) G ≪≫
    Functor.isoWhiskerLeft (e i).functor
      (Functor.isoWhiskerRight
        (FiniteClosedFamilies.singletonReconstructionIso X point closed i).symm
        (supportToOriginalEquivalence X point closed).inverse)

/-- Q2 and original reconstruction assemble the point K-groups in every positive degree. -/
def pointAssemblyKEquiv (injective : Function.Injective point) (n : ℕ) :
    (⨁ i, Additive (PointK X point closed i (n + 1))) ≃+ Additive (SupportK X point (n + 1)) :=
  (Quillen.FiniteSupport.decompositionKEquiv.{u, u+1}
    (PointCategory X point closed) n).symm.trans
    (reconstructionKEquiv X point closed injective (n + 1)).toAdditive

/-- Point assembly on a singleton is exactly the original small point-inclusion K-map. -/
theorem pointAssemblyKEquiv_of (injective : Function.Injective point) (n : ℕ) (i : I)
    (a : Additive (PointK X point closed i (n + 1))) :
    pointAssemblyKEquiv X point closed injective n (DirectSum.of _ i a) =
      Additive.ofMul ((pointInclusionExactFunctor X point closed i).KMap (n + 1) a.toMul) := by
  change Additive.ofMul ((reconstructionExactFunctor X point closed injective).KMap (n + 1)
    ((Quillen.FiniteSupport.decompositionKEquiv.{u, u+1} (PointCategory X point closed) n).symm
      (DirectSum.of _ i a)).toMul) = _
  rw [Quillen.FiniteSupport.decompositionKEquiv_symm_of]
  have h := ExactFunctor.KMap_eq_of_natIso (singletonReconstructionIso X point closed injective i)
    (n + 1)
  rw [ExactFunctor.KMap_comp] at h
  exact congrArg Additive.ofMul (DFunLike.congr_fun h a.toMul)

section Fields
variable (fields : I → Type u) [∀ i, Field (fields i)]
  (immersion : ∀ i, Spec (CommRingCat.of (fields i)) ⟶ X)
  [∀ i, IsClosedImmersion (immersion i)]
  (image : ∀ i y, immersion i y = point i)

local instance immersionRestriction_preservesFiniteLimits (i : I) :
    PreservesFiniteLimits (coherentRestrictionExact (openMap (immersion i))).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap (immersion i))

local instance immersionRestriction_preservesFiniteColimits (i : I) :
    PreservesFiniteColimits (coherentRestrictionExact (openMap (immersion i))).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap (immersion i))

local instance immersionRestriction_isLocalization (i : I) :
    (coherentRestrictionExact (openMap (immersion i))).toFunctor.IsLocalization
      (coherentRestrictionExact (openMap (immersion i))).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap (immersion i))

omit [IsNoetherian X] [∀ i, IsClosedImmersion (immersion i)] in
include image in
/-- The specified field immersion has exactly the specified singleton as its actual image. -/
theorem immersion_range (i : I) : Set.range (immersion i) = {point i} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact image i y
  · intro hx
    let y : Spec (CommRingCat.of (fields i)) := IsLocalRing.closedPoint (fields i)
    exact ⟨y, (image i y).trans (Set.mem_singleton_iff.mp hx).symm⟩

/-- Original ambient realization identifies native closed support with actual singleton support. -/
def nativePointEquivalence (i : I) : SmallSupport (immersion i) ≌ PointOriginal X point closed i :=
  (equivSmallModel.{u+1} (FiniteTypeSheaves X)).symm.congrFullSubcategory (by
    funext M
    apply propext
    rw [ObjectProperty.prop_inverseImage_iff, FiniteClosedSupport.closedSupportProperty_iff,
      coherentGlobalSmallSupport_iff, supported_iff,
      immersion_range X point fields immersion image i]
    rfl)

instance nativePointEquivalence_additive (i : I) :
    (nativePointEquivalence X point closed fields immersion image i).functor.Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse.map_add

/-- The original native closed-support realization is exact. -/
def nativePointToOriginalExactFunctor (i : I) : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap (immersion i))))
    (abelianExactStructure (PointOriginal X point closed i)) where
  toFunctor := (nativePointEquivalence X point closed fields immersion image i).functor
  map_conflation _ h := h.map_of_exact _

/-- One exact comparison from native closed support to its canonical upper-small point model. -/
def nativePointToModelExactFunctor (i : I) : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap (immersion i))))
    (pointExactStructure X point closed i) :=
  (nativePointToOriginalExactFunctor X point closed fields immersion image i).comp
    (pointModelExactFunctor X point closed i)

instance nativePointToModelExactFunctor_isEquivalence (i : I) :
    (nativePointToModelExactFunctor X point closed fields immersion image i).toFunctor.IsEquivalence
    :=
  ((nativePointEquivalence X point closed fields immersion image i).trans
    (equivSmallModel.{u+1} (PointOriginal X point closed i))).isEquivalence_functor

instance nativePointToModelExactFunctor_mapQ_isEquivalence (i : I) :
    (nativePointToModelExactFunctor X point closed fields immersion image i).mapQ.IsEquivalence :=
    by
  let F := nativePointToModelExactFunctor X point closed fields immersion image i
  apply F.mapQ_isEquivalence_of_equivalence
  · intro A B f hf
    exact (abelianExactStructure_inflation_iff _ f).2
      (F.toFunctor.mono_of_mono_map
        ((pointExactStructure X point closed i).mono_of_inflation hf))
  · intro A B f hf
    exact (abelianExactStructure_deflation_iff _ f).2
      (F.toFunctor.epi_of_epi_map
        ((pointExactStructure X point closed i).epi_of_deflation hf))

/-- The literal supported inclusion inside the unchanged original ambient small model. -/
def nativePointInclusion (i : I) : SmallSupport (immersion i) ⥤ SupportCategory X point :=
  ObjectProperty.ιOfLE (fun M hM => by
    have hs := (supported_iff (immersion i) _).1
      ((coherentGlobalSmallSupport_iff (openMap (immersion i)) M).1 hM)
    rw [immersion_range X point fields immersion image i] at hs
    exact fun x hx => ⟨i, (Set.mem_singleton_iff.mp (hs hx)).symm⟩)

instance nativePointInclusion_additive (i : I) :
    (nativePointInclusion X point fields immersion image i).Additive where
  map_add := by intros; rfl

/-- The literal native closed-support inclusion into the point-range support is exact. -/
def nativePointInclusionExactFunctor (i : I) : ExactFunctor
    (ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap (immersion i))))
    (supportExactStructure X point) where
  toFunctor := nativePointInclusion X point fields immersion image i
  map_conflation _ h := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (supportProperty X point).ι
    let := ObjectProperty.inclusion_preservesFiniteLimits
      (coherentGlobalSmallSupport (openMap (immersion i)))
    let := ObjectProperty.inclusion_preservesFiniteColimits
      (coherentGlobalSmallSupport (openMap (immersion i)))
    exact h.map_of_exact (coherentGlobalSmallSupport (openMap (immersion i))).ι

/-- The original support-inclusion square cancels only canonical model units and counits. -/
def nativePointInclusionComparisonIso (i : I) :
    ((nativePointToModelExactFunctor X point closed fields immersion image i).comp
      (pointInclusionExactFunctor X point closed i)).toFunctor ≅
        (nativePointInclusionExactFunctor X point fields immersion image i).toFunctor := by
  let A := equivSmallModel.{u+1} (FiniteTypeSheaves X)
  let e := equivSmallModel.{u+1} (PointOriginal X point closed i)
  let N := (nativePointEquivalence X point closed fields immersion image i).functor
  let G := (FiniteClosedSupport.closedSupportProperty X {point i} (closed i)).ι ⋙ A.functor
  apply Functor.fullyFaithfulCancelRight (supportProperty X point).ι
  change N ⋙ e.functor ⋙ e.inverse ⋙ G ≅
    (coherentGlobalSmallSupport (openMap (immersion i))).ι
  exact Functor.isoWhiskerLeft N (Functor.isoWhiskerRight e.unitIso.symm G) ≪≫
    Functor.isoWhiskerLeft N (Functor.leftUnitor G) ≪≫
    Functor.isoWhiskerLeft (coherentGlobalSmallSupport (openMap (immersion i))).ι A.counitIso ≪≫
    Functor.rightUnitor _

/-- Native geometric dévissage gives the original public field-scheme G-to-point-K equivalence. -/
def fieldPointKEquiv (i : I) (n : ℕ) : G (Spec (CommRingCat.of (fields i))) n ≃*
    PointK X point closed i n :=
  let F := nativePointToModelExactFunctor X point closed fields immersion image i
  (closedSupportGEquiv (immersion i) n).trans (F.KEquivOfMapQIsEquivalence n)

/-- The coordinate equivalence retains the native original pushforward and point comparison. -/
theorem fieldPointKEquiv_toMonoidHom (i : I) (n : ℕ) :
    (fieldPointKEquiv X point closed fields immersion image i n).toMonoidHom =
      ((nativePointToModelExactFunctor X point closed fields immersion image i).KMap n).comp
        ((smallPushforwardToSupportExact (immersion i)).KMap n) := by
  change ((nativePointToModelExactFunctor X point closed fields immersion image i).KMap n).comp
    (closedSupportGEquiv (immersion i) n).toMonoidHom = _
  rw [show (closedSupportGEquiv (immersion i) n).toMonoidHom =
    (smallPushforwardToSupportExact (immersion i)).KMap n from closedSupportGEquiv_coe _ _]

/-- The original native closed pushforward lifted into the actual point-range support. -/
def fieldSupportExactFunctor (i : I) : ExactFunctor
    (ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec (CommRingCat.of (fields i)))))
    (supportExactStructure X point) :=
  (smallPushforwardToSupportExact (immersion i)).comp
    (nativePointInclusionExactFunctor X point fields immersion image i)

/-- The supported lift retains literally the original transported ambient pushforward. -/
theorem fieldSupportExactFunctor_comp_ambient (i : I) :
    (fieldSupportExactFunctor X point fields immersion image i).comp
        (ObjectProperty.exactInclusion (supportProperty X point)) =
      (ExactFunctor.smallModel.{u+1} (coherentPushforwardExact (immersion i))).comp
        (CategoryTheory.SmallModel.abelianExactComparison.{u+1} (FiniteTypeSheaves X)) := rfl

/-- Coordinate dévissage followed by point inclusion is the original supported pushforward. -/
theorem fieldPointKEquiv_comp_inclusion (i : I) (n : ℕ) :
    ((pointInclusionExactFunctor X point closed i).KMap n).comp
        (fieldPointKEquiv X point closed fields immersion image i n).toMonoidHom =
      (fieldSupportExactFunctor X point fields immersion image i).KMap n := by
  have h := ExactFunctor.KMap_eq_of_natIso
    (nativePointInclusionComparisonIso X point closed fields immersion image i) n
  rw [ExactFunctor.KMap_comp] at h
  ext a
  calc
    _ = (pointInclusionExactFunctor X point closed i).KMap n
        ((nativePointToModelExactFunctor X point closed fields immersion image i).KMap n
          ((smallPushforwardToSupportExact (immersion i)).KMap n a)) :=
      congrArg ((pointInclusionExactFunctor X point closed i).KMap n)
        (DFunLike.congr_fun
          (fieldPointKEquiv_toMonoidHom X point closed fields immersion image i n) a)
    _ = (nativePointInclusionExactFunctor X point fields immersion image i).KMap n
        ((smallPushforwardToSupportExact (immersion i)).KMap n a) :=
      DFunLike.congr_fun h ((smallPushforwardToSupportExact (immersion i)).KMap n a)
    _ = _ := (DFunLike.congr_fun (ExactFunctor.KMap_comp _ _ n) a).symm

/-- Original supported inclusion into public scheme G-theory, with its standard comparison. -/
def supportInclusionKMap (n : ℕ) : SupportK X point n →* G X n :=
  (Quillen.SmallModelLocalization.standardKEquiv.{u+1}
    (FiniteTypeSheaves X) n).symm.toMonoidHom.comp
    ((ObjectProperty.exactInclusion (supportProperty X point)).KMap n)

/-- The ambient composite of a supported field summand is its original public pushforward. -/
theorem supportInclusionKMap_comp_fieldSupport (i : I) (n : ℕ) :
    (supportInclusionKMap X point n).comp
        ((fieldSupportExactFunctor X point fields immersion image i).KMap n) =
      coherentPushforwardGMap (immersion i) n := by
  have he : (nativePointInclusionExactFunctor X point fields immersion image i).comp
      (ObjectProperty.exactInclusion (supportProperty X point)) =
    ObjectProperty.exactInclusion (coherentGlobalSmallSupport (openMap (immersion i))) := rfl
  have hk := congrArg (fun F => F.KMap n) he
  rw [ExactFunctor.KMap_comp] at hk
  calc
    _ = (Quillen.SmallModelGLocalization.inclusionKMap.{u+1}
        (coherentRestrictionExact (openMap (immersion i))) n).comp
          ((smallPushforwardToSupportExact (immersion i)).KMap n) := by
      ext a
      change (Quillen.SmallModelLocalization.standardKEquiv.{u+1}
        (FiniteTypeSheaves X) n).symm
          ((ObjectProperty.exactInclusion (supportProperty X point)).KMap n
            ((fieldSupportExactFunctor X point fields immersion image i).KMap n a)) = _
      rw [show (fieldSupportExactFunctor X point fields immersion image i).KMap n =
        ((nativePointInclusionExactFunctor X point fields immersion image i).KMap n).comp
          ((smallPushforwardToSupportExact (immersion i)).KMap n) from
        ExactFunctor.KMap_comp _ _ n]
      exact congrArg
        (Quillen.SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).symm
        (DFunLike.congr_fun hk ((smallPushforwardToSupportExact (immersion i)).KMap n a))
    _ = (Quillen.SmallModelGLocalization.inclusionKMap.{u+1}
        (coherentRestrictionExact (openMap (immersion i))) n).comp
          (closedSupportGEquiv (immersion i) n).toMonoidHom :=
      congrArg (fun f => (Quillen.SmallModelGLocalization.inclusionKMap.{u+1}
        (coherentRestrictionExact (openMap (immersion i))) n).comp f)
        (show (smallPushforwardToSupportExact (immersion i)).KMap n =
          (closedSupportGEquiv (immersion i) n).toMonoidHom from
            (closedSupportGEquiv_coe _ _).symm)
    _ = _ := closedSupportGEquiv_pushforward (immersion i) n

/-- The direct sum of native field-coordinate dévissage equivalences. -/
def fieldDirectSumEquiv (n : ℕ) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) ≃+
      ⨁ i, Additive (PointK X point closed i (n + 1)) :=
  DFinsupp.mapRange.addEquiv
    (fun i => (fieldPointKEquiv X point closed fields immersion image i (n + 1)).toAdditive)

/-- Each direct-sum coordinate retains its original native dévissage equivalence. -/
theorem fieldDirectSumEquiv_of (n : ℕ) (i : I)
    (a : Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) :
    fieldDirectSumEquiv X point closed fields immersion image n (DirectSum.of _ i a) =
      DirectSum.of (fun j => Additive (PointK X point closed j (n + 1))) i
        (Additive.ofMul
          (fieldPointKEquiv X point closed fields immersion image i (n + 1) a.toMul)) := by
  change DirectSum.map (fun i =>
    (fieldPointKEquiv X point closed fields immersion image i (n + 1)).toAdditive.toAddMonoidHom)
      (DirectSum.of _ i a) = _
  exact DirectSum.map_of (fun i =>
    (fieldPointKEquiv X point closed fields immersion image i (n + 1)).toAdditive.toAddMonoidHom)
    i a

/-- Original closed field pushforwards assemble isomorphically in every positive degree. -/
def fieldAssemblyKEquiv (injective : Function.Injective point) (n : ℕ) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) ≃+
      Additive (SupportK X point (n + 1)) :=
  (fieldDirectSumEquiv X point closed fields immersion image n).trans
    (pointAssemblyKEquiv X point closed injective n)

/-- Assembly on each singleton is the original supported closed-pushforward K-map. -/
theorem fieldAssemblyKEquiv_of (injective : Function.Injective point) (n : ℕ) (i : I)
    (a : Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) :
    fieldAssemblyKEquiv X point closed fields immersion image injective n (DirectSum.of _ i a) =
      Additive.ofMul
        ((fieldSupportExactFunctor X point fields immersion image i).KMap (n + 1) a.toMul) := by
  change pointAssemblyKEquiv X point closed injective n
    (fieldDirectSumEquiv X point closed fields immersion image n (DirectSum.of _ i a)) = _
  rw [fieldDirectSumEquiv_of, pointAssemblyKEquiv_of]
  exact congrArg Additive.ofMul (DFunLike.congr_fun
    (fieldPointKEquiv_comp_inclusion X point closed fields immersion image i (n + 1)) a.toMul)

/-- The finite sum of original supported closed-pushforward K-maps. -/
def fieldAssemblyKMap (n : ℕ) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) →+
      Additive (SupportK X point (n + 1)) :=
  DirectSum.toAddMonoid (fun i =>
    ((fieldSupportExactFunctor X point fields immersion image i).KMap (n + 1)).toAdditive)

/-- The assembly equivalence has exactly the original pushforward sum forward. -/
theorem fieldAssemblyKEquiv_toAddMonoidHom (injective : Function.Injective point) (n : ℕ) :
    (fieldAssemblyKEquiv X point closed fields immersion image injective n).toAddMonoidHom =
      fieldAssemblyKMap X point fields immersion image n := by
  apply DirectSum.addHom_ext
  intro i a
  change fieldAssemblyKEquiv X point closed fields immersion image injective n
    (DirectSum.of _ i a) = fieldAssemblyKMap X point fields immersion image n (DirectSum.of _ i a)
  rw [fieldAssemblyKEquiv_of, fieldAssemblyKMap, DirectSum.toAddMonoid_of]
  rfl

/-- Assembly is the actual finite sum over the support of the direct-sum element. -/
theorem fieldAssemblyKEquiv_eq_sum (injective : Function.Injective point) (n : ℕ)
    (a : ⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) :
    fieldAssemblyKEquiv X point closed fields immersion image injective n a = ∑ i ∈ a.support,
      Additive.ofMul
        ((fieldSupportExactFunctor X point fields immersion image i).KMap (n + 1) (a i).toMul) := by
  calc
    _ = fieldAssemblyKMap X point fields immersion image n a :=
      DFunLike.congr_fun
        (fieldAssemblyKEquiv_toAddMonoidHom X point closed fields immersion image injective n) a
    _ = fieldAssemblyKMap X point fields immersion image n
        (∑ i ∈ a.support,
          DirectSum.of (fun j => Additive (G (Spec (CommRingCat.of (fields j))) (n + 1)))
            i (a i)) :=
      congrArg (fieldAssemblyKMap X point fields immersion image n)
        (DirectSum.sum_support_of a).symm
    _ = _ := by
      change (DirectSum.toAddMonoid (fun i =>
        ((fieldSupportExactFunctor X point fields immersion image i).KMap (n + 1)).toAdditive))
          (∑ i ∈ a.support,
            DirectSum.of (fun j => Additive (G (Spec (CommRingCat.of (fields j))) (n + 1)))
              i (a i)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact DirectSum.toAddMonoid_of (fun i =>
        ((fieldSupportExactFunctor X point fields immersion image i).KMap (n + 1)).toAdditive)
        i (a i)

/-- The sum of the original public coherent closed-pushforward G-maps. -/
def ambientAssemblyKMap (n : ℕ) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) (n + 1))) →+
      Additive (G X (n + 1)) :=
  DirectSum.toAddMonoid (fun i => (coherentPushforwardGMap (immersion i) (n + 1)).toAdditive)

/-- The original ambient support map composed with assembly is the public pushforward sum. -/
theorem supportInclusionKMap_comp_assembly (injective : Function.Injective point) (n : ℕ) :
    ((supportInclusionKMap X point (n + 1)).toAdditive).comp
        (fieldAssemblyKEquiv X point closed fields immersion image injective n).toAddMonoidHom =
      ambientAssemblyKMap X fields immersion n := by
  apply DirectSum.addHom_ext
  intro i a
  change Additive.ofMul (supportInclusionKMap X point (n + 1)
    (fieldAssemblyKEquiv X point closed fields immersion image injective n
      (DirectSum.of _ i a)).toMul) = ambientAssemblyKMap X fields immersion n (DirectSum.of _ i a)
  rw [fieldAssemblyKEquiv_of, ambientAssemblyKMap, DirectSum.toAddMonoid_of]
  exact congrArg Additive.ofMul (DFunLike.congr_fun
    (supportInclusionKMap_comp_fieldSupport X point fields immersion image i (n + 1)) a.toMul)

/-- The original closed-point pushforward assembly equivalence in degree one. -/
abbrev fieldK1AssemblyEquiv (injective : Function.Injective point) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) 1)) ≃+ Additive (SupportK X point 1) :=
  fieldAssemblyKEquiv X point closed fields immersion image injective 0

/-- The original closed-point pushforward assembly equivalence in degree two. -/
abbrev fieldK2AssemblyEquiv (injective : Function.Injective point) :
    (⨁ i, Additive (G (Spec (CommRingCat.of (fields i))) 2)) ≃+ Additive (SupportK X point 2) :=
  fieldAssemblyKEquiv X point closed fields immersion image injective 1

end Fields

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.FinitePointAssembly
