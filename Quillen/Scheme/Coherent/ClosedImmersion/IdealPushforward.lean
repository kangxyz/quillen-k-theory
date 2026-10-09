import Quillen.Scheme.Coherent.ClosedImmersion.AffinePushforward
import Quillen.GTheory.FiniteModules.IdealClosedSupport
import Quillen.Scheme.Coherent.Affine.ComparisonGTheory
import Quillen.CategoryTheory.SmallModel.Functoriality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual coherent pushforward from an arbitrary affine closed subscheme

For every ideal I, the actual pushforward along Spec(R/I) → Spec(R) restricts
to an exact fully faithful functor on coherent sheaves. It is an equivalence
onto coherent sheaves with global sections annihilated by I. The canonical
G-maps commute with quotient-ring restriction under affine comparison.
-/
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
  refine ⟨isQuasicoherent_pushforward _ M, ?_⟩
  let N : FGModuleCat (ClosedRing I) := ⟨moduleSpecΓFunctor.obj M, hM.2⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙
      ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (I))).hom).obj M) :=
    ((closedRestriction I).obj N).property
  exact Module.Finite.equiv
    ((pushforwardGlobalSectionsIso
      (CommRingCat.ofHom (Ideal.Quotient.mk (I)))).app M).symm.toLinearEquiv

/-- Actual closed pushforward preserves all-affine-chart coherence. -/
theorem coherent_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : coherent (Spec (closedRing R I)) M) :
    coherent (Spec R) ((Scheme.Modules.pushforward (closedMap R I)).obj M) :=
  (coherent_spec_iff R _).mpr
    (affineFiniteSheaf_pushforward R I ((coherent_spec_iff (closedRing R I) M).mp hM))

variable [IsNoetherianRing R]

/-- Closed pushforward on actual coherent sheaves. -/
def coherentPushforward : Coherent (Spec (closedRing R I)) ⥤ Coherent (Spec R) :=
  ObjectProperty.lift _
    (coherentToSheaves (Spec (closedRing R I)) ⋙
      Scheme.Modules.pushforward (closedMap R I))
    (fun M ↦ coherent_pushforward R I M.property)

/-- Forgetting coherence gives the actual sheaf pushforward, definitionally. -/
theorem coherentPushforward_comp_inclusion :
    coherentPushforward R I ⋙ coherentToSheaves (Spec R) =
      coherentToSheaves (Spec (closedRing R I)) ⋙
        Scheme.Modules.pushforward (closedMap R I) := rfl

/-- The actual geometric pushforward/global-sections comparison square. -/
def coherentPushforwardSquare :
    coherentPushforward R I ⋙ (coherentSpecModuleEquivalence R).functor ≅
      (coherentSpecModuleEquivalence (closedRing R I)).functor ⋙ closedRestriction I :=
  ((finiteModule R).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (coherentToSheaves (Spec (closedRing R I)))
      (pushforwardGlobalSectionsIso
        (CommRingCat.ofHom (Ideal.Quotient.mk (I)))))

instance coherentPushforward_full : (coherentPushforward R I).Full :=
  Functor.Full.of_comp_faithful_iso (coherentPushforwardSquare R I)

instance coherentPushforward_faithful : (coherentPushforward R I).Faithful :=
  Functor.Faithful.of_comp_iso (coherentPushforwardSquare R I)

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (coherentPushforward R I) := by
  have : PreservesFiniteLimits
      (coherentPushforward R I ⋙ (coherentSpecModuleEquivalence R).functor) :=
    preservesFiniteLimits_of_natIso (coherentPushforwardSquare R I).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (coherentPushforward R I)
    (coherentSpecModuleEquivalence R).functor

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (coherentPushforward R I) := by
  have : PreservesFiniteColimits
      (coherentPushforward R I ⋙ (coherentSpecModuleEquivalence R).functor) :=
    preservesFiniteColimits_of_natIso (coherentPushforwardSquare R I).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (coherentPushforward R I)
    (coherentSpecModuleEquivalence R).functor

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
def coherentKilledBy : ObjectProperty (Coherent (Spec R)) :=
  (killedBy I).inverseImage (coherentSpecModuleEquivalence R).functor

instance coherentKilledBy_isoClosed : (coherentKilledBy R I).IsClosedUnderIsomorphisms := by
  dsimp [coherentKilledBy]
  infer_instance

/-- The affine global-section equivalence restricts to annihilated objects. -/
def killedModuleEquivalence :
    (coherentKilledBy R I).FullSubcategory ≌ (killedBy I).FullSubcategory :=
  (coherentSpecModuleEquivalence R).congrFullSubcategory rfl

/-- The actual closed pushforward is annihilated by every element of the defining ideal. -/
theorem coherentPushforward_killed (M : Coherent (Spec (closedRing R I))) :
    coherentKilledBy R I ((coherentPushforward R I).obj M) := by
  let e := (coherentPushforwardSquare R I).app M
  intro r hr m
  apply (FGModuleCat.isoToLinearEquiv e).injective
  rw [map_smul, map_zero]
  exact closedRestriction_killed I
    ((coherentSpecModuleEquivalence (closedRing R I)).functor.obj M) r hr _

/-- Actual sheaf pushforward, with its codomain restricted to annihilated
objects rather than the larger supported category. -/
def coherentPushforwardToKilled :
    Coherent (Spec (closedRing R I)) ⥤ (coherentKilledBy R I).FullSubcategory :=
  ObjectProperty.lift _ (coherentPushforward R I) (coherentPushforward_killed R I)

/-- Forgetting the annihilation proof recovers actual coherent pushforward. -/
theorem coherentPushforwardToKilled_comp_inclusion :
    coherentPushforwardToKilled R I ⋙ (coherentKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The comparison square restricts to the actual annihilated full subcategories. -/
def coherentPushforwardToKilledSquare :
    coherentPushforwardToKilled R I ⋙ (killedModuleEquivalence R I).functor ≅
      (coherentSpecModuleEquivalence (closedRing R I)).functor ⋙ closedToKilled I :=
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
    Coherent (Spec (closedRing R I)) ≌ (coherentKilledBy R I).FullSubcategory :=
  (coherentPushforwardToKilled R I).asEquivalence

instance coherentKilled_hasFiniteProducts :
    HasFiniteProducts (coherentKilledBy R I).FullSubcategory where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (coherentClosedEquivalence R I).inverse

/-- The annihilated category is abelian via its proved actual closed-sheaf
equivalence, without claiming that it is a Serre subcategory. -/
instance coherentKilled_abelian : Abelian (coherentKilledBy R I).FullSubcategory :=
  abelianOfEquivalence (coherentClosedEquivalence R I).inverse

instance coherentPushforwardToKilled_additive : (coherentPushforwardToKilled R I).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (coherentPushforwardToKilled R I)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Actual closed pushforward is exact as an equivalence onto the annihilated
coherent category equipped with its standard abelian exact structure. -/
def coherentPushforwardToKilledExact :
    ExactFunctor (coherentExactStructure (Spec (closedRing R I)))
      (abelianExactStructure (coherentKilledBy R I).FullSubcategory) where
  toFunctor := coherentPushforwardToKilled R I
  map_conflation _ h := h.map_of_exact _

/-- The equivalence is induced by actual geometric pushforward. -/
theorem coherentClosedEquivalence_comp_inclusion :
    (coherentClosedEquivalence R I).functor ⋙ (coherentKilledBy R I).ι =
      coherentPushforward R I := rfl

/-- The annihilated coherent inclusion is the actual pushforward composed
with the inverse of its proved equivalence. -/
def coherentKilledInclusionComparison :
    (coherentClosedEquivalence R I).inverse ⋙ coherentPushforward R I ≅
      (coherentKilledBy R I).ι := by
  change (coherentClosedEquivalence R I).inverse ⋙
      ((coherentClosedEquivalence R I).functor ⋙ (coherentKilledBy R I).ι) ≅ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coherentClosedEquivalence R I).counitIso _ ≪≫
      Functor.leftUnitor _

instance coherentKilledInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (coherentKilledBy R I).ι :=
  preservesFiniteLimits_of_natIso (coherentKilledInclusionComparison R I)

instance coherentKilledInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (coherentKilledBy R I).ι :=
  preservesFiniteColimits_of_natIso (coherentKilledInclusionComparison R I)

/-- Inclusion of the annihilated coherent subcategory is exact. -/
def coherentKilledInclusionExact :
    ExactFunctor (abelianExactStructure (coherentKilledBy R I).FullSubcategory)
      (coherentExactStructure (Spec R)) where
  toFunctor := (coherentKilledBy R I).ι
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
  ExactFunctor.smallKMap.{u+1} (coherentPushforwardExact R I) n

/-- The exact comparison square induces equality of canonical upper-universe
K-maps. The module term here is formed in the same universe as public scheme G. -/
theorem coherentPushforwardGMap_square (n : ℕ) :
    (ExactFunctor.smallKMap.{u+1} (globalSectionsExact R) n).comp
      (coherentPushforwardGMap R I n) =
    (ExactFunctor.smallKMap.{u+1} (closedRestrictionExact I) n).comp
      (ExactFunctor.smallKMap.{u+1} (globalSectionsExact (closedRing R I)) n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u+1}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [ExactFunctor.smallKMap_comp, coherentPushforwardGMap] using h

/-- The same actual pushforward on the proved lowest-universe affine G-groups. -/
def specPushforwardGMap (n : ℕ) : SpecG (closedRing R I) n →* SpecG R n :=
  (coherentPushforwardExact R I).smallKMap n

/-- The affine G-comparison is precisely the canonical global-sections K-map. -/
theorem specGRingEquiv_eq_globalSections (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom =
      ExactFunctor.smallKMap.{u} (globalSectionsExact R) n := by
  rw [globalSectionsExact, ExactFunctor.smallKMap_comp]
  rfl

/-- Actual closed sheaf pushforward matches actual quotient-ring restriction
of scalars under the proved affine G-theory equivalences. -/
theorem specPushforwardGMap_square (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom.comp (specPushforwardGMap R I n) =
      ((closedRestrictionExact I).smallKMap n).comp
        (specGRingEquiv (closedRing R I) n).toMonoidHom := by
  rw [specGRingEquiv_eq_globalSections, specGRingEquiv_eq_globalSections]
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentPushforwardExact R I).comp (globalSectionsExact R))
    (G := (globalSectionsExact (closedRing R I)).comp (closedRestrictionExact I))
    (coherentPushforwardSquare R I) n
  simpa only [ExactFunctor.smallKMap_comp, specPushforwardGMap] using h

end Quillen.CoherentScheme.ClosedImmersion.Ideal
