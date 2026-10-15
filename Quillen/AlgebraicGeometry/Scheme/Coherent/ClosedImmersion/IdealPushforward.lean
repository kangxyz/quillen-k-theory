/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffinePushforward
public import Quillen.GTheory.FiniteModules.IdealClosedSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ComparisonGTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coherent pushforward from an arbitrary affine closed subscheme

For every ideal I, the actual pushforward along Spec(R/I) → Spec(R) restricts
to an exact fully faithful functor on coherent sheaves. It is an equivalence
onto coherent sheaves with global sections annihilated by I. The canonical
G-maps commute with quotient-ring restriction under affine comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.Ideal

open FiniteModuleLocalization.IdealClosedSupport

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The closed subscheme's affine coordinate ring. -/
abbrev closedRing : CommRingCat.{u} := CommRingCat.of (ClosedRing I)

/-- The actual closed immersion induced by the quotient map. -/
def closedMap : Spec (closedRing R I) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I)))

instance closedMap_isClosedImmersion : IsClosedImmersion (closedMap R I) := by
  unfold closedMap
  infer_instance

/-- Actual sheaf pushforward preserves the affine coherence property. -/
theorem affineFiniteSheaf_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineFiniteSheaf (closedRing R I) M) :
    affineFiniteSheaf R ((Scheme.Modules.pushforward (closedMap R I)).obj M) := by
  have : M.IsQuasicoherent := hM.1
  refine ⟨SchemeSheaf.isQuasicoherent_pushforward _ M, ?_⟩
  let N : FGModuleCat (ClosedRing I) := ⟨moduleSpecΓFunctor.obj M, hM.2⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙
      ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (I))).hom).obj M) :=
    ((closedRestriction I).obj N).property
  exact Module.Finite.equiv
    ((SchemeSheaf.pushforwardGlobalSectionsIso
      (CommRingCat.ofHom (Ideal.Quotient.mk (I)))).app M).symm.toLinearEquiv

/-- Actual closed pushforward preserves all-affine-chart coherence. -/
theorem affineLocallyFiniteType_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineLocallyFiniteType (Spec (closedRing R I)) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (closedMap R I)).obj M) :=
  (affineLocallyFiniteType_spec_iff R _).mpr
    (affineFiniteSheaf_pushforward R I ((affineLocallyFiniteType_spec_iff (closedRing R I) M).mp
      hM))

variable [IsNoetherianRing R]

/-- Closed pushforward on actual coherent sheaves. -/
def coherentPushforward : FiniteTypeSheaves (Spec (closedRing R I)) ⥤ FiniteTypeSheaves (Spec R) :=
  ObjectProperty.lift _
    (finiteTypeSheavesToModules (Spec (closedRing R I)) ⋙
      Scheme.Modules.pushforward (closedMap R I))
    (fun M ↦ affineLocallyFiniteType_pushforward R I M.property)

omit [IsNoetherianRing R] in
/-- The finite-type sheaf inclusion gives the actual sheaf pushforward, definitionally. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward R I ⋙ finiteTypeSheavesToModules (Spec R) =
      finiteTypeSheavesToModules (Spec (closedRing R I)) ⋙
        Scheme.Modules.pushforward (closedMap R I) := rfl

/-- The actual geometric pushforward/global-sections comparison square. -/
def coherentPushforwardSquare :
    coherentPushforward R I ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor ⋙ closedRestriction I :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules (Spec (closedRing R I)))
      (SchemeSheaf.pushforwardGlobalSectionsIso
        (CommRingCat.ofHom (Ideal.Quotient.mk (I)))))

instance coherentPushforward_full : (coherentPushforward R I).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardSquare R I)

instance coherentPushforward_faithful : (coherentPushforward R I).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardSquare R I)

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward R I) := by
  have : PreservesFiniteLimits
      (coherentPushforward R I ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) :=
    preservesFiniteLimits_of_natIso (coherentPushforwardSquare R I).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentPushforward R I)
    (finiteTypeSheavesSpecModuleEquivalence R).functor

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward R I) := by
  have : PreservesFiniteColimits
      (coherentPushforward R I ⋙ (finiteTypeSheavesSpecModuleEquivalence R).functor) :=
    preservesFiniteColimits_of_natIso (coherentPushforwardSquare R I).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentPushforward R I)
    (finiteTypeSheavesSpecModuleEquivalence R).functor

instance coherentPushforward_additive : (coherentPushforward R I).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforward R I)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact functor induced by actual closed sheaf pushforward. -/
def coherentPushforwardExact :
    ExactFunctor (coherentExactStructure (Spec (closedRing R I)))
      (coherentExactStructure (Spec R)) where
  toFunctor := coherentPushforward R I
  map_conflation _ h := h.map_of_exact _

open FiniteModuleLocalization.IdealClosedSupport
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- Annihilation by I on actual affine coherent sheaves, tested on the
actual global-section module. This is stronger than power-torsion support. -/
def finiteTypeSheavesKilledBy : ObjectProperty (FiniteTypeSheaves (Spec R)) :=
  (killedBy I).inverseImage (finiteTypeSheavesSpecModuleEquivalence R).functor

instance finiteTypeSheavesKilledBy_isoClosed : (finiteTypeSheavesKilledBy R
  I).IsClosedUnderIsomorphisms := by
  dsimp [finiteTypeSheavesKilledBy]
  infer_instance

/-- The affine global-section equivalence restricts to annihilated objects. -/
def killedModuleEquivalence :
    (finiteTypeSheavesKilledBy R I).FullSubcategory ≌ (killedBy I).FullSubcategory :=
  (finiteTypeSheavesSpecModuleEquivalence R).congrFullSubcategory rfl

omit [IsNoetherianRing R] in
/-- The actual closed pushforward is annihilated by every element of the defining ideal. -/
theorem coherentPushforward_killed (M : FiniteTypeSheaves (Spec (closedRing R I))) :
    finiteTypeSheavesKilledBy R I ((coherentPushforward R I).obj M) := by
  let e := (coherentPushforwardSquare R I).app M
  intro r hr m
  apply (FGModuleCat.isoToLinearEquiv e).injective
  rw [map_smul, map_zero]
  exact closedRestriction_killed I
    ((finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor.obj M) r hr _

/-- Actual sheaf pushforward, with its codomain restricted to annihilated
objects rather than the larger supported category. -/
def coherentPushforwardToKilled :
    FiniteTypeSheaves (Spec (closedRing R I)) ⥤ (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  ObjectProperty.lift _ (coherentPushforward R I) (coherentPushforward_killed R I)

omit [IsNoetherianRing R] in
/-- Forgetting the annihilation proof recovers actual finite-type sheaf pushforward. -/
theorem coherentPushforwardToKilled_comp_inclusion :
    coherentPushforwardToKilled R I ⋙ (finiteTypeSheavesKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The comparison square restricts to the actual annihilated full subcategories. -/
def coherentPushforwardToKilledSquare :
    coherentPushforwardToKilled R I ⋙ (killedModuleEquivalence R I).functor ≅
      (finiteTypeSheavesSpecModuleEquivalence (closedRing R I)).functor ⋙ closedToKilled I :=
  ((killedBy I).fullyFaithfulι.whiskeringRight _).preimageIso (coherentPushforwardSquare R I)

instance coherentPushforwardToKilled_full : (coherentPushforwardToKilled R I).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardToKilledSquare R I)

instance coherentPushforwardToKilled_faithful : (coherentPushforwardToKilled R I).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardToKilledSquare R I)

instance coherentPushforwardToKilled_essSurj : (coherentPushforwardToKilled R I).EssSurj := by
  have : (coherentPushforwardToKilled R I ⋙ (killedModuleEquivalence R I).functor).EssSurj :=
    Functor.essSurj_of_iso (coherentPushforwardToKilledSquare R I).symm
  exact Functor.essSurj_of_comp_fully_faithful (coherentPushforwardToKilled R I)
    (killedModuleEquivalence R I).functor

instance coherentPushforwardToKilled_isEquivalence :
    (coherentPushforwardToKilled R I).IsEquivalence := {}

/-- The equivalence onto exactly the I-annihilated coherent objects, induced
by the actual geometric closed pushforward. -/
def coherentClosedEquivalence :
    FiniteTypeSheaves (Spec (closedRing R I)) ≌ (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  (coherentPushforwardToKilled R I).asEquivalence

instance coherentKilled_hasFiniteProducts :
    HasFiniteProducts (finiteTypeSheavesKilledBy R I).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (coherentClosedEquivalence R I).inverse

/-- The annihilated category is abelian via its proved actual closed-sheaf
equivalence, without claiming that it is a Serre subcategory. -/
instance instAbelianCoherentKilledBy : Abelian (finiteTypeSheavesKilledBy R I).FullSubcategory :=
  abelianOfEquivalence (coherentClosedEquivalence R I).inverse

instance coherentPushforwardToKilled_additive : (coherentPushforwardToKilled R I).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforwardToKilled R I)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual closed pushforward is exact as an equivalence onto the annihilated
coherent category equipped with its standard abelian exact structure. -/
def coherentPushforwardToKilledExact :
    ExactFunctor (coherentExactStructure (Spec (closedRing R I)))
      (abelianExactStructure (finiteTypeSheavesKilledBy R I).FullSubcategory) where
  toFunctor := coherentPushforwardToKilled R I
  map_conflation _ h := h.map_of_exact _

omit [IsNoetherianRing R] in
/-- The equivalence is induced by actual geometric pushforward. -/
theorem coherentClosedEquivalence_comp_inclusion :
    (coherentClosedEquivalence R I).functor ⋙ (finiteTypeSheavesKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The annihilated finite-type sheaf inclusion is the actual pushforward composed
with the inverse of its proved equivalence. -/
def coherentKilledInclusionComparison :
    (coherentClosedEquivalence R I).inverse ⋙ coherentPushforward R I ≅
      (finiteTypeSheavesKilledBy R I).ι := by
  change (coherentClosedEquivalence R I).inverse ⋙
      ((coherentClosedEquivalence R I).functor ⋙ (finiteTypeSheavesKilledBy R I).ι) ≅ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coherentClosedEquivalence R I).counitIso _ ≪≫
      Functor.leftUnitor _

instance coherentKilledInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (finiteTypeSheavesKilledBy R I).ι :=
  preservesFiniteLimits_of_natIso (coherentKilledInclusionComparison R I)

instance coherentKilledInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (finiteTypeSheavesKilledBy R I).ι :=
  preservesFiniteColimits_of_natIso (coherentKilledInclusionComparison R I)

/-- Inclusion of the annihilated coherent subcategory is exact. -/
def coherentKilledInclusionExact :
    ExactFunctor (abelianExactStructure (finiteTypeSheavesKilledBy R I).FullSubcategory)
      (coherentExactStructure (Spec R)) where
  toFunctor := (finiteTypeSheavesKilledBy R I).ι
  map_conflation _ h := h.map_of_exact _

open FiniteModuleLocalization.IdealClosedSupport

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual global sections on the global coherent category as an exact functor. -/
def globalSectionsExact :
    ExactFunctor (coherentExactStructure (Spec R)) (finiteModuleExactStructure.{u, u} R) :=
  (coherentToAffineExact R).comp (affineGlobalSectionsExact R)

variable (I : Ideal R)

/-- The canonical closed pushforward on the public global G-groups. -/
def coherentPushforwardGMap (n : ℕ) :
    CoherentScheme.G (Spec (closedRing R I)) n →* CoherentScheme.G (Spec R) n :=
  CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (coherentPushforwardExact R I) n

/-- The exact comparison square induces equality of canonical upper-universe
K-maps. The module term here is formed in the same universe as public scheme G. -/
theorem coherentPushforwardGMap_square (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact R) n).comp
      (coherentPushforwardGMap R I n) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (closedRestrictionExact I) n).comp
      (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (globalSectionsExact (closedRing R
        I)) n) := by
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, coherentPushforwardGMap]
    using h

/-- The same actual pushforward on the proved lowest-universe affine G-groups. -/
def specPushforwardGMap (n : ℕ) : SpecG (closedRing R I) n →* SpecG R n :=
  (coherentPushforwardExact R I).smallKMap n

/-- The affine G-comparison is precisely the canonical global-sections K-map. -/
theorem specGRingEquiv_eq_globalSections (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u} (globalSectionsExact R) n := by
  rw [globalSectionsExact, CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp]
  rfl

/-- Actual closed sheaf pushforward matches actual quotient-ring restriction
of scalars under the proved affine G-theory equivalences. -/
theorem specPushforwardGMap_square (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom.comp (specPushforwardGMap R I n) =
      ((closedRestrictionExact I).smallKMap n).comp
        (specGRingEquiv (closedRing R I) n).toMonoidHom := by
  rw [specGRingEquiv_eq_globalSections, specGRingEquiv_eq_globalSections]
  have h := CategoryTheory.ExactCategory.ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [CategoryTheory.ExactCategory.ExactFunctor.smallKMap_comp, specPushforwardGMap] using h

end Quillen.CoherentScheme.ClosedImmersion.Ideal
