/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality

/-!
# Genuine flat pullback of locally perfect complexes

Actual flat geometric pullback is exact on all module sheaves. Hence its
termwise complex functor preserves every actual quasi-isomorphism, descends
to the existing derived localization, and preserves the original genuinely
local strict-model predicate. The resulting maps on the original Waldhausen
K-groups satisfy identity, composition, open restriction, and comparison
naturality. No global strict representative is required.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

instance pullbackComplex_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (pullbackComplex f) := by unfold pullbackComplex; infer_instance

instance pullbackFunctor_preservesHomology {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Actual flat pullback preserves every quasi-isomorphism of module-sheaf complexes. -/
instance pullbackComplex_quasiIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K L : Complex Y} (s : K ⟶ L) [QuasiIso s] : QuasiIso ((pullbackComplex f).map s) := by
  unfold pullbackComplex
  infer_instance

/-- The actual flat termwise pullback, followed by localization, inverts quasi-isomorphisms. -/
theorem pullback_toDerived_inverts {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)).IsInvertedBy
      (pullbackComplex f ⋙ toDerived X) := by
  intro K L s hs
  let : QuasiIso s := hs
  exact toDerived_map_isIso ((pullbackComplex f).map s)

/-- The actual functor on the existing quasi-isomorphism localization. -/
def derivedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : Derived Y ⥤ Derived X :=
  Localization.Construction.lift (pullbackComplex f ⋙ toDerived X) (pullback_toDerived_inverts f)

/-- The constructed derived functor retains the original geometric pullback. -/
theorem toDerived_derivedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    toDerived Y ⋙ derivedFlatPullback f = pullbackComplex f ⋙ toDerived X :=
  Localization.Construction.fac _ _

/-- The factorization through the existing derived localization. -/
def derivedFlatPullbackFactors {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    toDerived Y ⋙ derivedFlatPullback f ≅ pullbackComplex f ⋙ toDerived X :=
  eqToIso (toDerived_derivedFlatPullback f)

/-- Flat geometric pullback of an actual isomorphism in the derived localization. -/
def flatPullbackDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] {K L : Complex Y}
    (e : (toDerived Y).obj K ≅ (toDerived Y).obj L) :
    (toDerived X).obj ((pullbackComplex f).obj K) ≅
      (toDerived X).obj ((pullbackComplex f).obj L) :=
  ((derivedFlatPullbackFactors f).app K).symm ≪≫
    (derivedFlatPullback f).mapIso e ≪≫ (derivedFlatPullbackFactors f).app L

/-- Genuine flat pullback preserves the original local derived strict-model condition. -/
theorem locallyPerfect_flatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K : Complex Y} (hK : locallyPerfect Y K) :
    locallyPerfect X ((pullbackComplex f).obj K) := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK (f x)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨(pullbackComplex (f ∣_ U)).obj P.obj,
    strictPerfect_pullback (f ∣_ U) P.property⟩, ?_⟩
  exact ⟨(toDerived (f ⁻¹ᵁ U).toScheme).mapIso ((pullbackComplexRestrictIso f U).app K) ≪≫
    flatPullbackDerivedIso (f ∣_ U) eP⟩

/-- Actual geometric flat pullback on the full category of locally perfect complexes. -/
def perfectFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : Perfect Y ⥤ Perfect X :=
  (locallyPerfect X).lift ((locallyPerfect Y).ι ⋙ pullbackComplex f)
    (fun K => locallyPerfect_flatPullback f K.property)

instance perfectFlatPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (perfectFlatPullback f).Additive := by unfold perfectFlatPullback; infer_instance

/-- Flat exactness for the original inherited perfect-complex exact structures. -/
def perfectExactFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex Y)) (locallyPerfect Y))
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (locallyPerfect X)) where
  toFunctor := perfectFlatPullback f
  map_conflation S hS := by
    change ((S.map (locallyPerfect Y).ι).map (pullbackComplex f)).ShortExact
    exact hS.map_of_exact _

/-- Actual flat pullback is exact for the original locally-perfect Waldhausen categories. -/
theorem perfectFlatPullback_waldhausenExact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Waldhausen.IsExact (perfectWaldhausen Y).cof (perfectWaldhausen Y).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectFlatPullback f) where
  zero h := (perfectFlatPullback f).map_isZero h
  cofibration s hs := (perfectExactFlatPullback f).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact pullbackComplex_quasiIso f s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure (Complex Y))
      (locallyPerfect Y) hi h).map (pullbackComplex f)

/-- The original perfect K-groups carry the genuine flat geometric pullback K-map. -/
def perfectKFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    PerfectK Y n →* PerfectK X n := Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n

/-- Geometric identity comparison on the original locally-perfect category. -/
def perfectFlatPullbackIdIso (X : Scheme.{u}) :
    perfectFlatPullback (𝟙 X) ≅ 𝟭 (Perfect X) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (pullbackComplexIdIso X))

/-- Geometric composition comparison on the original locally-perfect category. -/
def perfectFlatPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    perfectFlatPullback (f ≫ g) ≅ perfectFlatPullback g ⋙ perfectFlatPullback f :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect Z).ι (pullbackComplexCompIso f g))

/-- Geometric open restriction agrees with flat pullback on all locally-perfect complexes. -/
def perfectRestrictIsoFlatPullback {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    perfectRestrict j ≅ perfectFlatPullback j :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect Y).ι (restrictIsoPullbackComplex j))

@[simp high]
theorem perfectKFlatPullback_id (X : Scheme.{u}) (n : ℕ) :
    perfectKFlatPullback (𝟙 X) n = MonoidHom.id (PerfectK X n) :=
  (Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (perfectWaldhausen X).cof (perfectWaldhausen X).weq)
    (perfectFlatPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem perfectKFlatPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] (n : ℕ) :
    perfectKFlatPullback (f ≫ g) n = (perfectKFlatPullback f n).comp (perfectKFlatPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact (f ≫ g))
    ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
    (perfectFlatPullbackCompIso f g) n).trans (Waldhausen.KMap_comp _ _ n)

/-- The original geometric open-restriction map is recovered without changing the model. -/
theorem perfectKFlatPullback_eq_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) : perfectKFlatPullback j n = perfectKRestrict j n :=
  Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact j)
    (perfectRestrict_waldhausenExact j) (perfectRestrictIsoFlatPullback j).symm n

/-- Flat pullback commutes with restriction to an inverse-image open. -/
def perfectFlatPullbackRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (U : Y.Opens) :
    perfectFlatPullback f ⋙ perfectRestrict (f ⁻¹ᵁ U).ι ≅
      perfectRestrict U.ι ⋙ perfectFlatPullback (f ∣_ U) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect (f ⁻¹ᵁ U).toScheme).ι
    (Functor.isoWhiskerLeft (locallyPerfect Y).ι (pullbackComplexRestrictIso f U))

/-- Actual flat pullback/restriction naturality on the existing perfect K-groups. -/
theorem perfectKFlatPullback_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (U : Y.Opens) (n : ℕ) :
    (perfectKRestrict (f ⁻¹ᵁ U).ι n).comp (perfectKFlatPullback f n) =
      (perfectKFlatPullback (f ∣_ U) n).comp (perfectKRestrict U.ι n) := by
  unfold perfectKFlatPullback perfectKRestrict
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]
  exact Waldhausen.KMap_eq_of_iso _ _ (perfectFlatPullbackRestrictIso f U) n

/-- The original strict-to-locally-perfect comparison commutes with actual flat pullback. -/
theorem strictToPerfectKMap_flatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (strictToPerfectKMap Y n) =
      (strictToPerfectKMap X n).comp (strictKPullback f n) := by
  unfold perfectKFlatPullback strictToPerfectKMap strictKPullback Waldhausen.subcategoryKMap
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]

/-- The original public vector-bundle-to-perfect comparison is natural for flat morphisms. -/
theorem vectorBundleToPerfectKMap_flatPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (vectorBundleToPerfectKMap Y n) =
      (vectorBundleToPerfectKMap X n).comp (Quillen.Scheme.pullbackK f n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← MonoidHom.comp_assoc, strictToPerfectKMap_flatPullback,
    MonoidHom.comp_assoc, vectorBundleToStrictKMap_pullback, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
