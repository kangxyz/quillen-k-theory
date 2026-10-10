/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.StupidTruncationFixedBounds

/-! # The actual brutal filtration inside each finite term stratum

The original brutal and single-layer functors stay inside the specified
actual term-bound category. Their original maps give a genuine structural
cofibration sequence of exact endofunctors, with identity and zero endpoints.
Only isomorphism weak equivalences are used, and kernel closure is absent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An actual brutal subcomplex retains every specified term bound. -/
theorem HasTermBounds.stupidTruncGE {K : CochainComplex A ℤ} {a b : ℤ}
    (hK : HasTermBounds K a b) (n : ℤ) : HasTermBounds (stupidTruncGE K n) a b := by
  intro i hi
  let : IsSplitMono ((stupidTruncGEInclusion K n).f i) :=
    stupidTruncGEInclusion_degreewiseSplitMono K n i
  exact IsZero.of_mono ((stupidTruncGEInclusion K n).f i) (hK i hi)

/-- The original single-term quotient has the same bounds, by its actual epimorphism. -/
theorem HasTermBounds.stupidLayer {K : CochainComplex A ℤ} {a b : ℤ}
    (hK : HasTermBounds K a b) (n : ℤ) : HasTermBounds ((stupidTruncGELayerFunctor n).obj K) a b
      := by
  intro i hi
  have hs := stupidTruncGELayerSequence_degree_shortExact K n i
  let : Epi ((stupidTruncGELayerProjection K n).f i) := hs.epi_g
  exact IsZero.of_epi ((stupidTruncGELayerProjection K n).f i) (hK.stupidTruncGE n i hi)

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- The original brutal truncation, now as an actual endofunctor of the stratum. -/
def finiteTermTruncation (a b n : ℤ) :
    (fixedTermsBounds P a b).FullSubcategory ⥤ (fixedTermsBounds P a b).FullSubcategory :=
  (fixedTermsBounds P a b).lift
    ((fixedTermsBounds P a b).ι ⋙ boundedTermsStupidTruncGEFunctor P n)
    (fun K ↦ K.property.stupidTruncGE n)

/-- The original single-term quotient as an actual endofunctor of the stratum. -/
def finiteTermLayer (a b n : ℤ) :
    (fixedTermsBounds P a b).FullSubcategory ⥤ (fixedTermsBounds P a b).FullSubcategory :=
  (fixedTermsBounds P a b).lift
    ((fixedTermsBounds P a b).ι ⋙ boundedTermsStupidLayerFunctor P n)
    (fun K ↦ K.property.stupidLayer n)

instance finiteTermTruncation_additive (a b n : ℤ) : (finiteTermTruncation P a b n).Additive :=
  inferInstanceAs (Functor.Additive ((fixedTermsBounds P a b).lift _ _))
instance finiteTermLayer_additive (a b n : ℤ) : (finiteTermLayer P a b n).Additive :=
  inferInstanceAs (Functor.Additive ((fixedTermsBounds P a b).lift _ _))

@[simp] theorem finiteTermTruncation_inclusion (a b n : ℤ) :
    finiteTermTruncation P a b n ⋙ (fixedTermsBounds P a b).ι =
      (fixedTermsBounds P a b).ι ⋙ boundedTermsStupidTruncGEFunctor P n := rfl
@[simp] theorem finiteTermLayer_inclusion (a b n : ℤ) :
    finiteTermLayer P a b n ⋙ (fixedTermsBounds P a b).ι =
      (fixedTermsBounds P a b).ι ⋙ boundedTermsStupidLayerFunctor P n := rfl

/-- All original increasing transitions remain inside the stratum. -/
def finiteTermTransition (a b : ℤ) {n m : ℤ} (h : n ≤ m) :
    finiteTermTruncation P a b m ⟶ finiteTermTruncation P a b n where
  app K := (fixedTermsBounds P a b).homMk
    ((boundedTermsStupidTruncGETransitionNat P h).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((boundedTermsStupidTruncGETransitionNat P h).naturality f.hom)

/-- The original single-term projection remains inside the stratum. -/
def finiteTermProjection (a b n : ℤ) :
    finiteTermTruncation P a b n ⟶ finiteTermLayer P a b n where
  app K := (fixedTermsBounds P a b).homMk ((boundedTermsStupidLayerProjectionNat P n).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((boundedTermsStupidLayerProjectionNat P n).naturality f.hom)

@[reassoc] theorem finiteTerm_comp_zero (a b n : ℤ) :
    finiteTermTransition P a b (by omega : n ≤ n + 1) ≫ finiteTermProjection P a b n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _
    (NatTrans.congr_app (boundedTermsStupidLayer_comp_zero P n) K.obj)

/-- The actual lower-endpoint inclusion is naturally invertible inside the stratum. -/
def finiteTermIdentityIso (a b n : ℤ) (hn : n ≤ a) :
    finiteTermTruncation P a b n ≅ 𝟭 (fixedTermsBounds P a b).FullSubcategory :=
  NatIso.ofComponents (fun K ↦ (fixedTermsBounds P a b).isoMk
    ((fixedTermsStupidTruncGEIdentityIso P a b n hn).app K)) (by
      intro K L f
      exact ObjectProperty.hom_ext _
        ((fixedTermsStupidTruncGEIdentityIso P a b n hn).hom.naturality f))

@[simp] theorem finiteTermIdentityIso_hom (a b n : ℤ) (hn : n ≤ a)
    (K : (fixedTermsBounds P a b).FullSubcategory) :
    (((finiteTermIdentityIso P a b n hn).hom.app K).hom.hom) =
      stupidTruncGEInclusion K.obj.obj n := rfl

/-- The actual upper-endpoint object is genuinely zero in this same stratum. -/
theorem finiteTermTruncation_isZero (a b n : ℤ) (hn : b < n)
    (K : (fixedTermsBounds P a b).FullSubcategory) :
    IsZero ((finiteTermTruncation P a b n).obj K) := by
  apply IsZero.of_full_of_faithful_of_isZero (fixedTermsBounds P a b).ι
  apply IsZero.of_full_of_faithful_of_isZero (boundedTerms P).ι
  exact stupidTruncGE_isZero_above_bound K.obj.obj a b n K.property hn

/-- The upper endpoint is naturally the actual zero functor on the same stratum. -/
def finiteTermZeroIso (a b n : ℤ) (hn : b < n) :
    finiteTermTruncation P a b n ≅
      (Functor.const (fixedTermsBounds P a b).FullSubcategory).obj
        (0 : (fixedTermsBounds P a b).FullSubcategory) :=
  NatIso.ofComponents (fun K ↦ (finiteTermTruncation_isZero P a b n hn K).iso (isZero_zero _))
    (by
      intro K L f
      exact (finiteTermTruncation_isZero P a b n hn K).eq_of_src _ _)

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- Exactness inside the same actual finite stratum. -/
def finiteTermTruncationExact (a b n : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b) (fixedTermsExactStructure P a b) where
  toFunctor := finiteTermTruncation P a b n
  map_conflation S hS := stupidTruncGE_shortExact
    (S.map ((fixedTermsBounds P a b).ι ⋙ (boundedTerms P).ι)) hS n

/-- Exactness of the actual single-term quotient inside the same stratum. -/
def finiteTermLayerExact (a b n : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b) (fixedTermsExactStructure P a b) where
  toFunctor := finiteTermLayer P a b n
  map_conflation S hS := stupidTruncGELayer_shortExact
    (S.map ((fixedTermsBounds P a b).ι ⋙ (boundedTerms P).ι)) hS n

/-- The pointwise sequence retains the actual original inclusion and projection. -/
theorem finiteTermLayer_conflation (a b n : ℤ) (K : (fixedTermsBounds P a b).FullSubcategory) :
    (fixedTermsExactStructure P a b).conflation
      (ShortComplex.mk ((finiteTermTransition P a b (by omega : n ≤ n + 1)).app K)
        ((finiteTermProjection P a b n).app K)
        (NatTrans.congr_app (finiteTerm_comp_zero P a b n) K)) :=
  stupidTruncGELayerSequence_shortExact K.obj.obj n

/-- Genuine finite-stratum structural additivity data, with original maps. -/
theorem finiteTerm_isCofibrationSequence (a b n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (fixedTermsExactStructure P a b))
      (ofExactCategory (fixedTermsExactStructure P a b))
      (finiteTermTransition P a b (by omega : n ≤ n + 1)) (finiteTermProjection P a b n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (finiteTerm_comp_zero P a b n)
    (finiteTermLayer_conflation P a b n)
    (finiteTermTruncationExact P a b (n + 1)) (finiteTermTruncationExact P a b n)
    (finiteTermLayerExact P a b n) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen
