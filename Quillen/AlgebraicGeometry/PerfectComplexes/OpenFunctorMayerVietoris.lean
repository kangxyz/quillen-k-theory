/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorSum
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris

/-! # Actual supported excision and Mayer-Vietoris under exact restriction squares

The ambient restriction isomorphism lifts to the original supported categories.
The actual excision inverse is then natural because its forward map is the
proved supported restriction equivalence. No injectivity of ordinary local
restriction maps is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenFunctorNaturality
open Waldhausen

variable {V X V' X' : Scheme.{u}} (j : V ⟶ X) (j' : V' ⟶ X')
  [IsOpenImmersion j] [IsOpenImmersion j'] (T : X.Opens) (T' : X'.Opens)
  (D : ExactRestrictionSquare T.ι T'.ι)
  (E : ExactRestrictionSquare (j ⁻¹ᵁ T).ι (j' ⁻¹ᵁ T').ι)
  (e : D.ambient ⋙ perfectRestrict j' ≅ perfectRestrict j ⋙ E.ambient)

/-- The given actual ambient comparison lifts to the original supported restriction functors. -/
def supportedRestrictionIso :
    D.supported ⋙ perfectSupportedRestrict j' T' ≅ perfectSupportedRestrict j T ⋙ E.supported :=
  Functor.fullyFaithfulCancelRight (perfectSupported (j' ⁻¹ᵁ T').ι).ι
    (Functor.isoWhiskerLeft (supportInclusion T.ι)
      (Functor.isoWhiskerRight e (locallyPerfect V').ι))

include e

/-- The original supported restriction square, not a supplied K-map compatibility premise. -/
theorem supportedRestrictionKMap (n : ℕ) :
    (perfectSupportedKRestrict j' T' n).comp (D.supportedKMap n) =
      (E.supportedKMap n).comp (perfectSupportedKRestrict j T n) := by
  unfold perfectSupportedKRestrict ExactRestrictionSquare.supportedKMap
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (supportedRestrictionIso j j' T T' D E e) n

variable (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  (hc' : ∀ x : X', x ∈ Set.range j' ∨ x ∈ T')

/-- The inverse of the actual supported restriction equivalence commutes with the original functor.
-/
theorem supportedExcisionInverse (n : ℕ) (a : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    D.supportedKMap n ((perfectSupportedExcisionKEquiv j T hc n).symm a) =
      (perfectSupportedExcisionKEquiv j' T' hc' n).symm (E.supportedKMap n a) := by
  apply (perfectSupportedExcisionKEquiv j' T' hc' n).injective
  have h := DFunLike.congr_fun (supportedRestrictionKMap j j' T T' D E e n)
    ((perfectSupportedExcisionKEquiv j T hc n).symm a)
  change perfectSupportedExcisionKEquiv j' T' hc' n
      (D.supportedKMap n ((perfectSupportedExcisionKEquiv j T hc n).symm a)) =
    E.supportedKMap n (perfectSupportedExcisionKEquiv j T hc n
      ((perfectSupportedExcisionKEquiv j T hc n).symm a)) at h
  simpa only [MulEquiv.apply_symm_apply] using h

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace V'] [QuasiSeparatedSpace V']
  [CompactSpace T'.toScheme] [CompactSpace (j' ⁻¹ᵁ T').toScheme]

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme]
  [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace T'.toScheme] in
/-- Actual support-forgetting and excision give the unchanged Mayer-Vietoris boundary square. -/
theorem connectingHom_natural (n : ℕ) (a : PerfectK (j ⁻¹ᵁ T).toScheme (n + 1)) :
    KMap D.ambient_exact n (PerfectMayerVietoris.connectingHom j T hc n a) =
      PerfectMayerVietoris.connectingHom j' T' hc' n (KMap E.onOpen_exact (n + 1) a) := by
  have hforget := DFunLike.congr_fun (D.supportedKMap_forget n)
    ((perfectSupportedExcisionKEquiv j T hc n).symm
      (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n a))
  have hexc := supportedExcisionInverse j j' T T' D E e hc hc' n
    (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n a)
  have hboundary := DFunLike.congr_fun (E.qcqsConnectingHom n) a
  simp only [MonoidHom.comp_apply] at hforget hboundary
  change KMap D.ambient_exact n
      (perfectSupportedKMap T.ι n ((perfectSupportedExcisionKEquiv j T hc n).symm
        (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n a))) =
    perfectSupportedKMap T'.ι n ((perfectSupportedExcisionKEquiv j' T' hc' n).symm
      (qcqsPerfectConnectingHom (j' ⁻¹ᵁ T').ι n (KMap E.onOpen_exact (n + 1) a)))
  rw [← hforget, hexc, hboundary]

end Quillen.PerfectComplexes.OpenFunctorNaturality
