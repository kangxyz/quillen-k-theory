/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorReindex
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBoundaryNaturality

/-! # Native localization on the literal inverse-image open

The actual native base-change isomorphism identifies the open vertex with
the literal inverse image of the compact base open. The supported functor
still has exactly the original ambient two-summand complex and chain map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme.ProjectiveLine

instance nativeOpenBaseInclusion_isOpenImmersion (X : QuasiCompactSchemes.{u})
    (Z : X.obj.Opens) [CompactSpace Z.toScheme] :
    IsOpenImmersion (nativeOpenBaseInclusion X Z).hom := by
  change IsOpenImmersion Z.ι
  infer_instance

/-- The literal inverse-image open is compact through the actual native base-change isomorphism. -/
instance nativeProjectionOpen_compactSpace (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    [CompactSpace Z.toScheme] :
    CompactSpace ((nativeProjection.app X).hom ⁻¹ᵁ Z).toScheme :=
  (AlgebraicGeometry.Scheme.homeoOfIso (nativeProjectionOpenIso X Z)).compactSpace

end Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine
open Quillen.Scheme Quillen.Scheme.ProjectiveLine
open Waldhausen Waldhausen.ExtensionCategory OpenFunctorNaturality

variable (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens) [CompactSpace Z.toScheme]

/-- The actual first summand restricted to the literal inverse-image open. -/
def nativeFirstPreimageSquare :
    ExactRestrictionSquare Z.ι ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι :=
  (nativeFirstRestrictionSquare (nativeOpenBaseInclusion X Z)).reindexTargetOpen
    (nativeProjectionOpenIso X Z).symm ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
    (nativeProjectionOpenIso_inv_inclusion X Z)

/-- The actual left-tensor second summand restricted to the literal inverse-image open. -/
def nativeSecondPreimageSquare :
    ExactRestrictionSquare Z.ι ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι :=
  (nativeSecondRestrictionSquare (nativeOpenBaseInclusion X Z)).reindexTargetOpen
    (nativeProjectionOpenIso X Z).symm ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι
    (nativeProjectionOpenIso_inv_inclusion X Z)

/-- Original native Phi preserves the actual inverse-image localized weak class. -/
theorem nativeTwoSummands_preimageOpenExact : IsExact
    (productStructure (perfectOpenWeakWaldhausen Z.ι) (perfectOpenWeakWaldhausen Z.ι)).cof
    (productStructure (perfectOpenWeakWaldhausen Z.ι) (perfectOpenWeakWaldhausen Z.ι)).weq
    (perfectOpenWeakWaldhausen ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).cof
    (perfectOpenWeakWaldhausen ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).weq
    (nativeTwoSummands X) :=
  Additivity.sumFunctor_isExact _ _
    ((fst_exact _ _).comp (nativeFirstPreimageSquare X Z).coarseExact)
    ((snd_exact _ _).comp (nativeSecondPreimageSquare X Z).coarseExact)

/-- The original native sum, restricted to the actual inverse-image supported categories. -/
def nativeSupportedPreimageTwoSummands :
    (perfectSupported Z.ι).FullSubcategory × (perfectSupported Z.ι).FullSubcategory ⥤
      (perfectSupported ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).FullSubcategory :=
  (nativeFirstPreimageSquare X Z).supportedPair (nativeSecondPreimageSquare X Z)

/-- The supported inverse-image operator retains the literal original ambient complex. -/
@[simp] theorem nativeSupportedPreimageTwoSummands_obj
    (K : (perfectSupported Z.ι).FullSubcategory × (perfectSupported Z.ι).FullSubcategory) :
    ((nativeSupportedPreimageTwoSummands X Z).obj K).obj =
      ((nativeTwoSummands X).obj (⟨K.1.obj, K.1.property.1⟩,
        ⟨K.2.obj, K.2.property.1⟩)).obj := rfl

/-- The supported inverse-image operator retains the literal original ambient chain map. -/
@[simp] theorem nativeSupportedPreimageTwoSummands_map
    {K L : (perfectSupported Z.ι).FullSubcategory × (perfectSupported Z.ι).FullSubcategory}
    (g : K ⟶ L) :
    ((nativeSupportedPreimageTwoSummands X Z).map g).hom =
      ((nativeTwoSummands X).map
        ((locallyPerfect X.obj).homMk g.1.hom, (locallyPerfect X.obj).homMk g.2.hom)).hom := rfl

/-- The original inverse-image supported functor is exact. -/
theorem nativeSupportedPreimageTwoSummands_exact : IsExact
    (productStructure (perfectSupportedWaldhausen Z.ι) (perfectSupportedWaldhausen Z.ι)).cof
    (productStructure (perfectSupportedWaldhausen Z.ι) (perfectSupportedWaldhausen Z.ι)).weq
    (perfectSupportedWaldhausen ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).cof
    (perfectSupportedWaldhausen ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).weq
    (nativeSupportedPreimageTwoSummands X Z) :=
  (nativeFirstPreimageSquare X Z).supportedPair_exact (nativeSecondPreimageSquare X Z)

/-- The original product K-equivalence gives the actual inverse-image supported Phi map. -/
def nativeSupportedPreimageTwoSummandKMap (n : ℕ) :
    PerfectSupportedK Z.ι n × PerfectSupportedK Z.ι n →*
      PerfectSupportedK ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n :=
  (nativeFirstPreimageSquare X Z).supportedPairKMap (nativeSecondPreimageSquare X Z) n

/-- Forgetting inverse-image support gives the unchanged original native Phi, including K0. -/
theorem nativeSupportedPreimageTwoSummandKMap_forget (n : ℕ) (a b : PerfectSupportedK Z.ι n) :
    perfectSupportedKMap ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n
        (nativeSupportedPreimageTwoSummandKMap X Z n (a, b)) =
      nativeTwoSummandKMap X n (perfectSupportedKMap Z.ι n a,
        perfectSupportedKMap Z.ι n b) := by
  rw [nativeTwoSummandKMap_apply]
  exact (nativeFirstPreimageSquare X Z).supportedPairKMap_forget
    (nativeSecondPreimageSquare X Z) n a b

variable [QuasiSeparatedSpace X.obj]

/-- Original native Phi commutes with the original boundary on the literal inverse-image open. -/
theorem nativeTwoSummandKMap_preimageConnecting (n : ℕ) (a b : PerfectK Z.toScheme (n + 1)) :
    nativeSupportedPreimageTwoSummandKMap X Z n
        (qcqsPerfectConnectingHom Z.ι n a, qcqsPerfectConnectingHom Z.ι n b) =
      qcqsPerfectConnectingHom ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n
        (perfectKRestrict (nativeProjectionOpenIso X Z).inv (n + 1)
          (nativeTwoSummandKMap (nativeOpenBase X Z) (n + 1) (a, b))) := by
  have h := (nativeFirstPreimageSquare X Z).supportedPairKMap_connecting
    (nativeSecondPreimageSquare X Z) n a b
  change nativeSupportedPreimageTwoSummandKMap X Z n
      (qcqsPerfectConnectingHom Z.ι n a, qcqsPerfectConnectingHom Z.ι n b) =
    qcqsPerfectConnectingHom ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n
      (KMap ((nativeFirstSummand_exact (nativeOpenBase X Z)).comp
          (perfectRestrict_waldhausenExact (nativeProjectionOpenIso X Z).inv)) (n + 1) a *
        KMap ((nativeSecondSummand_exact (nativeOpenBase X Z)).comp
          (perfectRestrict_waldhausenExact (nativeProjectionOpenIso X Z).inv)) (n + 1) b) at h
  rw [← KMap_comp_KMap (nativeFirstSummand_exact (nativeOpenBase X Z))
      (perfectRestrict_waldhausenExact (nativeProjectionOpenIso X Z).inv) (n + 1),
    ← KMap_comp_KMap (nativeSecondSummand_exact (nativeOpenBase X Z))
      (perfectRestrict_waldhausenExact (nativeProjectionOpenIso X Z).inv) (n + 1)] at h
  rw [nativeTwoSummandKMap_apply, map_mul]
  exact h

end Quillen.PerfectComplexes.ProjectiveLine
