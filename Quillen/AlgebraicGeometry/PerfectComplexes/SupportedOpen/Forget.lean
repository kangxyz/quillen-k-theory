/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.LongExactSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence
public import Quillen.Waldhausen.Fibration.ConnectingNaturality

/-! # Original relative support-forgetting functor and boundary square -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The unchanged supported inclusion is exact for the relative weak classes. -/
lemma perfectSupportedOpenForget_exact : IsExact
    (perfectSupportedOpenWeakWaldhausen j T).cof (perfectSupportedOpenWeakWaldhausen j T).weq
    (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
    (ObjectProperty.ιOfLE (show perfectSupported T.ι ≤ locallyPerfect X from fun _ h => h.1)) where
  zero := (subcategoryInclusion_exact (perfectSupported T.ι) (locallyPerfect X) (fun _ h =>
    h.1)).zero
  cofibration := (subcategoryInclusion_exact (perfectSupported T.ι) (locallyPerfect X) (fun _ h =>
    h.1)).cofibration
  weak _ h := h
  pushout := (subcategoryInclusion_exact (perfectSupported T.ι) (locallyPerfect X) (fun _ h =>
    h.1)).pushout

def perfectSupportedOpenKForget (n : ℕ) : PerfectSupportedOpenK j T n →* PerfectOpenK j n :=
  KMap (perfectSupportedOpenForget_exact j T) n

lemma perfectSupportedOpenKForget_comp_changeWeak (n : ℕ) :
    (perfectSupportedOpenKForget j T n).comp (perfectSupportedOpenKMap j T n) =
      (perfectOpenKMap j n).comp (perfectSupportedKMap T.ι n) := by
  unfold perfectSupportedOpenKForget perfectSupportedOpenKMap perfectOpenKMap perfectSupportedKMap
    subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

lemma perfectSupportedOpenKForget_comp_restrict (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectSupportedOpenKForget j T n) =
      (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedOpenKRestrict j T n) := by
  unfold perfectSupportedOpenKForget perfectOpenKRestrict perfectSupportedKMap
    perfectSupportedOpenKRestrict subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- Forget the first support condition on the original union-supported fiber. -/
def perfectSupportedUnionForgetKMap (n : ℕ) :
    PerfectSupportedK (T ⊔ j.opensRange).ι n →* PerfectSupportedK j n :=
  subcategoryKMap (perfectSupported (T ⊔ j.opensRange).ι) (perfectSupported j)
    (fun K h => ⟨h.1, ((perfectSupported_sup_opensRange_iff j T K).mp h).2⟩) n

lemma perfectSupportedUnionForgetKMap_comp_flatten (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp (perfectSupportedOpenAcyclicSupportedKEquiv j T
      n).toMonoidHom =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectOpenNested j)
          (subcategoryInclusion_exact (perfectSupported T.ι) (locallyPerfect X) (fun _ h => h.1))
          (perfectSupportedOpenForget_exact j T)) n) := by
  change (KMap (subcategoryInclusion_exact (perfectSupported (T ⊔ j.opensRange).ι) (perfectSupported
    j)
    (fun K h => ⟨h.1, ((perfectSupported_sup_opensRange_iff j T K).mp h).2⟩)) n).comp
    (KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n) =
    (KMap (perfectAcyclicToSupported_exact j) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- Forgetting the prescribed support commutes with the genuine original
connecting homomorphism, including the K1-to-K0 boundary. -/
lemma perfectSupportedOpenConnectingHom_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp (perfectSupportedOpenConnectingHom j T n) =
      (perfectOpenConnectingHom j n).comp (perfectSupportedOpenKForget j T (n+1)) := by
  unfold perfectSupportedOpenConnectingHom perfectOpenConnectingHom perfectSupportedOpenKForget
  rw [← MonoidHom.comp_assoc,perfectSupportedUnionForgetKMap_comp_flatten,MonoidHom.comp_assoc]
  rw [changeWeakConnectingHom_natural (perfectSupportedOpenNested j T) (perfectOpenNested j)
    (subcategoryInclusion_exact (perfectSupported T.ι) (locallyPerfect X) (fun _ h => h.1))
    (perfectSupportedOpenForget_exact j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)]
  rw [MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
