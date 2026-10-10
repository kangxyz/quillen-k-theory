/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.AuxiliaryNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairNaturality

/-! # Literal supported restriction with a prescribed support inequality -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (S : U.Opens) (T : X.Opens) (h : S ≤ j ⁻¹ᵁ T)

/-- Only the actual support predicate is weakened after original restriction. -/
def perfectSupportedRestrictOfLE : (perfectSupported T.ι).FullSubcategory ⥤
    (perfectSupported S.ι).FullSubcategory :=
  perfectSupportedRestrict j T ⋙ ObjectProperty.ιOfLE (perfectSupported_antitone h)

/-- Exactness uses original supported restriction and the genuine inherited inclusion. -/
theorem perfectSupportedRestrictOfLE_exact : IsExact
    (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq
    (perfectSupportedWaldhausen S.ι).cof (perfectSupportedWaldhausen S.ι).weq
    (perfectSupportedRestrictOfLE j S T h) :=
  (perfectSupportedRestrict_exact j T).comp
    (subcategoryInclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι) (perfectSupported S.ι)
      (perfectSupported_antitone h))

/-- The original actual-chain supported map on K-theory. -/
def perfectSupportedKRestrictOfLE (n : ℕ) : PerfectSupportedK T.ι n →* PerfectSupportedK S.ι n :=
  KMap (perfectSupportedRestrictOfLE_exact j S T h) n

lemma perfectSupportedKRestrictOfLE_eq_comp (n : ℕ) :
    perfectSupportedKRestrictOfLE j S T h n =
      (perfectSupportedChangeOpenKMap h n).comp (perfectSupportedKRestrict j T n) :=
  (Quillen.Waldhausen.KMap_comp_KMap (perfectSupportedRestrict_exact j T)
    (subcategoryInclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι) (perfectSupported S.ι)
      (perfectSupported_antitone h)) n).symm

/-- The actual pair square underlying this supported restriction. -/
def supportRestrictedPair : supportOpenPair S ⟶ supportOpenPair T :=
  supportChangeOpenPair h ≫ supportRestrictionPair j T

omit [IsOpenImmersion j] in
@[simp] theorem supportRestrictedPair_right :
    (supportRestrictedPair j S T h).hom.right = j := by
  change 𝟙 U ≫ j = j
  simp

omit [IsOpenImmersion j] in
/-- Both original support inclusions remain the actual maps of the pair square. -/
theorem supportRestrictedPair_left :
    (supportRestrictedPair j S T h).hom.left = j.resLE T S h := by
  apply (cancel_mono T.ι).mp
  have hw : (supportRestrictedPair j S T h).hom.left ≫ T.ι =
      S.ι ≫ (supportRestrictedPair j S T h).hom.right := (supportRestrictedPair j S T h).hom.w
  rw [hw, j.resLE_comp_ι h, supportRestrictedPair_right]

/-- The right map determines a morphism of the actual open-pair category. -/
theorem supportOpenPair_hom_ext {U X : Scheme.{u}} {S : U.Opens} {T : X.Opens}
    {f g : supportOpenPair S ⟶ supportOpenPair T} (he : f.hom.right = g.hom.right) : f = g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · apply (cancel_mono T.ι).mp
    have hf : f.hom.left ≫ T.ι = S.ι ≫ f.hom.right := f.hom.w
    have hg : g.hom.left ≫ T.ι = S.ι ≫ g.hom.right := g.hom.w
    rw [hf, hg, he]
  · exact he

variable [CompactSpace U] [CompactSpace X]

/-- The packaged chain-level map is exactly the old public supported pair pullback. -/
theorem perfectSupportedKRestrictOfLE_eq_pullback (n : ℕ) :
    perfectSupportedKRestrictOfLE j S T h n =
      perfectSupportedKPullback (qcSupportedBaseSquare (supportRestrictedPair j S T h)) n := by
  rw [perfectSupportedKRestrictOfLE_eq_comp, perfectSupportedChangeOpenKMap_eq_pullback,
    perfectSupportedKRestrict_eq_pullback, ← perfectSupportedKPullback_comp]
  rfl

/-- Any original open pair square with open ambient map is the same literal
chain restriction, followed only by the actual support inclusion. -/
theorem perfectSupportedKPullback_eq_restrictOfLE
    (f : supportOpenPair S ⟶ supportOpenPair T) [IsOpenImmersion f.hom.right] (n : ℕ) :
    perfectSupportedKPullback (qcSupportedBaseSquare f) n =
      perfectSupportedKRestrictOfLE f.hom.right S T (supportPair_le_preimage f) n := by
  let : CompactSpace (supportOpenPair S).obj.right := inferInstanceAs (CompactSpace U)
  let : CompactSpace (supportOpenPair T).obj.right := inferInstanceAs (CompactSpace X)
  rw [perfectSupportedKRestrictOfLE_eq_pullback]
  congr 1
  apply ObjectProperty.hom_ext
  apply supportOpenPair_hom_ext
  exact (supportRestrictedPair_right _ _ _ _).symm

end Quillen.PerfectComplexes

namespace Quillen.PerfectComplexes
open Waldhausen
variable {X : Scheme.{u}} {S T : X.Opens}

/-- Equality of the actual support opens makes the original inclusion a
bijection, with the opposite original inclusion as its inverse. -/
theorem perfectSupportedChangeOpenKMap_bijective (h : S ≤ T) (h' : T ≤ S) (n : ℕ) :
    Function.Bijective (perfectSupportedChangeOpenKMap h n) := by
  have hleft : (perfectSupportedChangeOpenKMap h' n).comp (perfectSupportedChangeOpenKMap h n) =
      MonoidHom.id _ := by
    rw [← perfectSupportedChangeOpenKMap_comp, perfectSupportedChangeOpenKMap_refl]
  have hright : (perfectSupportedChangeOpenKMap h n).comp (perfectSupportedChangeOpenKMap h' n) =
      MonoidHom.id _ := by
    rw [← perfectSupportedChangeOpenKMap_comp, perfectSupportedChangeOpenKMap_refl]
  exact ⟨Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hleft x),
    Function.RightInverse.surjective (fun x ↦ DFunLike.congr_fun hright x)⟩

end Quillen.PerfectComplexes
