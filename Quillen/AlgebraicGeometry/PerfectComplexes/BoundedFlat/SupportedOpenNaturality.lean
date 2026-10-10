/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenFibration
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairPullback
public import Quillen.Waldhausen.Fibration.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction

/-!
# Actual bounded-flat supported boundary and restriction naturality

The original relative boundary is natural under arbitrary commuting ambient
support/localization squares. Actual fiber flattening identifies its fiber map
with the original union-support pullback. Literal restriction agrees with the
existing pullback comparison. No compactness hypothesis is required.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration

lemma boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (n : ℕ) :
    (boundedFlatPerfectSupportedToPerfectSupportedKMap (T ⊔ j.opensRange).ι n).comp
      (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedFlatPerfectSupportedOpenNested j T)
        (perfectSupportedOpenNested j T)
        (boundedFlatPerfectSupportedInclusion_exact T.ι)
          (boundedFlatPerfectSupportedOpenInclusion_exact j T)) n) := by
  change (KMap (boundedFlatPerfectSupportedInclusion_exact (T ⊔ j.opensRange).ι) n).comp
      (KMap (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact j T) n) =
    (KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

lemma boundedFlatPerfectSupportedOpenConnectingHom_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (n : ℕ) :
    (boundedFlatPerfectSupportedToPerfectSupportedKMap (T ⊔ j.opensRange).ι n).comp
        (boundedFlatPerfectSupportedOpenConnectingHom j T n) =
      (perfectSupportedOpenConnectingHom j T n).comp
        (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T (n+1)) := by
  unfold boundedFlatPerfectSupportedOpenConnectingHom perfectSupportedOpenConnectingHom
    boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap
  rw [← MonoidHom.comp_assoc, boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_comparison,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedFlatPerfectSupportedOpenNested j T) (perfectSupportedOpenNested j T)
      (boundedFlatPerfectSupportedInclusion_exact T.ι)
        (boundedFlatPerfectSupportedOpenInclusion_exact j T),
    ← MonoidHom.comp_assoc]

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

lemma boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_pullback (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n).comp
      (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
    (boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv j' S n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedFlatPerfectSupportedOpenNested j T)
        (boundedFlatPerfectSupportedOpenNested j' S) (boundedFlatPerfectSupportedPullback_exact f)
        (boundedFlatPerfectSupportedOpenPullback_exact j' j f g w)) n) := by
  change (KMap (boundedFlatPerfectSupportedPullback_exact (supportedPairUnionSquare j' j f g w))
    n).comp
      (KMap (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact j T) n) =
    (KMap (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact j' S) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

lemma boundedFlatPerfectSupportedOpenConnectingHom_pullback (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n).comp
        (boundedFlatPerfectSupportedOpenConnectingHom j T n) =
      (boundedFlatPerfectSupportedOpenConnectingHom j' S n).comp
        (boundedFlatPerfectSupportedOpenKPullback j' j f g w (n+1)) := by
  unfold boundedFlatPerfectSupportedOpenConnectingHom boundedFlatPerfectSupportedOpenKPullback
  rw [← MonoidHom.comp_assoc, boundedFlatPerfectSupportedOpenAcyclicSupportedKEquiv_pullback,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedFlatPerfectSupportedOpenNested j T) (boundedFlatPerfectSupportedOpenNested j' S)
      (boundedFlatPerfectSupportedPullback_exact f) (boundedFlatPerfectSupportedOpenPullback_exact
        j' j f g w),
    ← MonoidHom.comp_assoc]

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

lemma boundedFlatPerfectSupportedOpenRestriction_exact : Waldhausen.IsExact
    (boundedFlatPerfectSupportedOpenWaldhausen j T).cof (boundedFlatPerfectSupportedOpenWaldhausen j
      T).weq
    (boundedFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
    (boundedFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
    (boundedFlatPerfectSupportedPullback (supportRestrictionPair j T)) where
  zero := (boundedFlatPerfectSupportedPullback_exact (supportRestrictionPair j T)).zero
  cofibration := (boundedFlatPerfectSupportedPullback_exact (supportRestrictionPair j
    T)).cofibration
  pushout := (boundedFlatPerfectSupportedPullback_exact (supportRestrictionPair j T)).pushout
  weak {K L} p hp := by
    have : QuasiIso ((restrict j).map p.hom) := hp
    let e := restrictIsoPullbackComplex j
    change QuasiIso ((pullbackComplex j).map p.hom)
    exact quasiIso_of_arrow_mk_iso ((restrict j).map p.hom) ((pullbackComplex j).map p.hom)
      (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)

/-- The supported relative K-map induced by actual open restriction. -/
def boundedFlatPerfectSupportedOpenKRestrict (n : ℕ) :
    BoundedFlatPerfectSupportedOpenK j T n →* BoundedFlatPerfectSupportedK (j ⁻¹ᵁ T).ι n :=
  Waldhausen.KMap (boundedFlatPerfectSupportedOpenRestriction_exact j T) n

lemma boundedFlatPerfectSupportedOpenKRestrict_comparison (n : ℕ) :
    (perfectSupportedOpenKRestrict j T n).comp
      (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap j T n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp
        (boundedFlatPerfectSupportedOpenKRestrict j T n) := by
  unfold perfectSupportedOpenKRestrict boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap
    boundedFlatPerfectSupportedToPerfectSupportedKMap boundedFlatPerfectSupportedOpenKRestrict
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFlatPerfectSupportedOriginalRestrictionIso j T) n

variable {U' X' : Scheme.{u}} (j' : U' ⟶ X') [IsOpenImmersion j'] {S : X'.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.hom.right = g ≫ j)

/-- The natural restriction-pullback comparison for the given supported pair square. -/
def boundedFlatPerfectSupportedOpenPairIso :
    boundedFlatPerfectSupportedPullback f ⋙ boundedFlatPerfectSupportedPullback
      (supportRestrictionPair j' S) ≅
      boundedFlatPerfectSupportedPullback (supportRestrictionPair j T) ⋙
        boundedFlatPerfectSupportedPullback (supportedPairTargetSquare j' j f g w) :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported (j' ⁻¹ᵁ S).ι).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported T.ι).ι
      ((pullbackComplexCompIso j' f.hom.right).symm ≪≫
        eqToIso (congrArg pullbackComplex w) ≪≫ pullbackComplexCompIso g j))

lemma boundedFlatPerfectSupportedOpenKRestrict_pullback (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback (supportedPairTargetSquare j' j f g w) n).comp
        (boundedFlatPerfectSupportedOpenKRestrict j T n) =
      (boundedFlatPerfectSupportedOpenKRestrict j' S n).comp
        (boundedFlatPerfectSupportedOpenKPullback j' j f g w n) := by
  unfold boundedFlatPerfectSupportedKPullback boundedFlatPerfectSupportedOpenKRestrict
    boundedFlatPerfectSupportedOpenKPullback
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFlatPerfectSupportedOpenPairIso j T j' f g w).symm n

end Quillen.PerfectComplexes

end
