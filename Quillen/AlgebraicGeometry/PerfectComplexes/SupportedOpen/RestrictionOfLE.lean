/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.RestrictedPairs


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.RestrictionOfLE


public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.AuxiliaryNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairNaturality

/-! # Literal supported restriction with a prescribed support inequality -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (S : U.Opens) (T : X.Opens) (h : S ≤ j ⁻¹ᵁ T)

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
