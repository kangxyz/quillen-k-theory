/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFunctorSum
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOpenNaturality

/-! # The original native two-summand localization boundary

Both actual native summands preserve the original localized weak equivalences.
Their literal supported sum commutes with the original qcqs localization
boundary, with domain K(n+1) and supported target K(n), including n = 0.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes.OpenFunctorNaturality
open Quillen.Waldhausen
open Quillen.Waldhausen.ExtensionCategory

open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open Waldhausen Waldhausen.ExtensionCategory OpenFunctorNaturality

variable {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) [IsOpenImmersion f.hom]

/-- The first original summand with its canonical open-restriction comparison. -/
def nativeFirstRestrictionSquare :
    ExactRestrictionSquare f.hom (nativeLineFunctor.map f).hom where
  ambient := nativeFirstSummand X
  onOpen := nativeFirstSummand U
  ambient_exact := nativeFirstSummand_exact X
  onOpen_exact := nativeFirstSummand_exact U
  restrictionIso := nativeFirstSummandOpenIso f

/-- The actual left-tensor second summand with its original line restriction comparison. -/
def nativeSecondRestrictionSquare :
    ExactRestrictionSquare f.hom (nativeLineFunctor.map f).hom where
  ambient := nativeSecondSummand X
  onOpen := nativeSecondSummand U
  ambient_exact := nativeSecondSummand_exact X
  onOpen_exact := nativeSecondSummand_exact U
  restrictionIso := nativeSecondSummandOpenIso f

/-- The unchanged native sum preserves quasi-isomorphisms on the actual base-change open. -/
theorem nativeTwoSummands_openExact : IsExact
    (productStructure (perfectOpenWeakWaldhausen f.hom)
      (perfectOpenWeakWaldhausen f.hom)).cof
    (productStructure (perfectOpenWeakWaldhausen f.hom)
      (perfectOpenWeakWaldhausen f.hom)).weq
    (perfectOpenWeakWaldhausen (nativeLineFunctor.map f).hom).cof
    (perfectOpenWeakWaldhausen (nativeLineFunctor.map f).hom).weq (nativeTwoSummands X) :=
  Additivity.sumFunctor_isExact _ _
    ((fst_exact _ _).comp (nativeFirstRestrictionSquare f).coarseExact)
    ((snd_exact _ _).comp (nativeSecondRestrictionSquare f).coarseExact)

/-- Restrict the literal original native sum to complexes acyclic on the prescribed open. -/
def nativeSupportedTwoSummands :
    (perfectSupported f.hom).FullSubcategory × (perfectSupported f.hom).FullSubcategory ⥤
      (perfectSupported (nativeLineFunctor.map f).hom).FullSubcategory :=
  (nativeFirstRestrictionSquare f).supportedPair (nativeSecondRestrictionSquare f)

/-- The supported producer retains exactly the original native two-summand complex. -/
@[simp] theorem nativeSupportedTwoSummands_obj
    (K : (perfectSupported f.hom).FullSubcategory × (perfectSupported f.hom).FullSubcategory) :
    ((nativeSupportedTwoSummands f).obj K).obj =
      ((nativeTwoSummands X).obj (⟨K.1.obj, K.1.property.1⟩,
        ⟨K.2.obj, K.2.property.1⟩)).obj := rfl

/-- The supported producer retains exactly the original native two-summand chain map. -/
@[simp] theorem nativeSupportedTwoSummands_map
    {K L : (perfectSupported f.hom).FullSubcategory × (perfectSupported f.hom).FullSubcategory}
    (g : K ⟶ L) :
    ((nativeSupportedTwoSummands f).map g).hom =
      ((nativeTwoSummands X).map
        ((locallyPerfect X.obj).homMk g.1.hom, (locallyPerfect X.obj).homMk g.2.hom)).hom := rfl

/-- Exactness of the literal supported native two-summand producer. -/
theorem nativeSupportedTwoSummands_exact : IsExact
    (productStructure (perfectSupportedWaldhausen f.hom)
      (perfectSupportedWaldhausen f.hom)).cof
    (productStructure (perfectSupportedWaldhausen f.hom)
      (perfectSupportedWaldhausen f.hom)).weq
    (perfectSupportedWaldhausen (nativeLineFunctor.map f).hom).cof
    (perfectSupportedWaldhausen (nativeLineFunctor.map f).hom).weq
    (nativeSupportedTwoSummands f) :=
  (nativeFirstRestrictionSquare f).supportedPair_exact (nativeSecondRestrictionSquare f)

/-- The actual supported native map uses the original product K-equivalence. -/
def nativeSupportedTwoSummandKMap (n : ℕ) :
    PerfectSupportedK f.hom n × PerfectSupportedK f.hom n →*
      PerfectSupportedK (nativeLineFunctor.map f).hom n :=
  (nativeFirstRestrictionSquare f).supportedPairKMap (nativeSecondRestrictionSquare f) n

/-- Forgetting support recovers exactly the original native two-summand K-map in every degree. -/
theorem nativeSupportedTwoSummandKMap_forget (n : ℕ) (a b : PerfectSupportedK f.hom n) :
    perfectSupportedKMap (nativeLineFunctor.map f).hom n
        (nativeSupportedTwoSummandKMap f n (a, b)) =
      nativeTwoSummandKMap X n (perfectSupportedKMap f.hom n a,
        perfectSupportedKMap f.hom n b) := by
  rw [nativeTwoSummandKMap_apply]
  exact (nativeFirstRestrictionSquare f).supportedPairKMap_forget
    (nativeSecondRestrictionSquare f) n a b

variable [QuasiSeparatedSpace X.obj]

/-- The original native two-summand map commutes with the original qcqs supported boundary. -/
theorem nativeTwoSummandKMap_connecting (n : ℕ) (a b : PerfectK U.obj (n + 1)) :
    nativeSupportedTwoSummandKMap f n
        (qcqsPerfectConnectingHom f.hom n a, qcqsPerfectConnectingHom f.hom n b) =
      qcqsPerfectConnectingHom (nativeLineFunctor.map f).hom n
        (nativeTwoSummandKMap U (n + 1) (a, b)) := by
  rw [nativeTwoSummandKMap_apply]
  exact (nativeFirstRestrictionSquare f).supportedPairKMap_connecting
    (nativeSecondRestrictionSquare f) n a b

end Quillen.PerfectComplexes.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine

variable (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens) [CompactSpace Z.toScheme]

/-- The compact base open as an original native base. -/
def nativeOpenBase : QuasiCompactSchemes.{u} := ⟨Z.toScheme, inferInstance⟩

/-- The literal inclusion of the compact base open. -/
def nativeOpenBaseInclusion : nativeOpenBase X Z ⟶ X := ⟨Z.ι⟩

/-- Canonical native base change is the actual inverse-image open of the projection. -/
def nativeProjectionOpenIso : (nativeLineFunctor.obj (nativeOpenBase X Z)).obj ≅
    ((nativeProjection.app X).hom ⁻¹ᵁ Z).toScheme :=
  (nativeMap_isPullback (nativeOpenBaseInclusion X Z)).isoIsPullback _ _
    (isPullback_morphismRestrict (nativeProjection.app X).hom Z).flip

/-- The canonical comparison retains the actual inclusion into the native line. -/
@[reassoc (attr := simp)] theorem nativeProjectionOpenIso_hom_inclusion :
    (nativeProjectionOpenIso X Z).hom ≫ ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι =
      (nativeLineFunctor.map (nativeOpenBaseInclusion X Z)).hom :=
  (nativeMap_isPullback (nativeOpenBaseInclusion X Z)).isoIsPullback_hom_fst _ _ _

/-- The canonical comparison retains the actual restriction of the original projection. -/
@[reassoc (attr := simp)] theorem nativeProjectionOpenIso_hom_projection :
    (nativeProjectionOpenIso X Z).hom ≫ (nativeProjection.app X).hom ∣_ Z =
      (nativeProjection.app (nativeOpenBase X Z)).hom :=
  (nativeMap_isPullback (nativeOpenBaseInclusion X Z)).isoIsPullback_hom_snd _ _ _

/-- The inverse comparison retains the same original open inclusion. -/
@[reassoc (attr := simp)] theorem nativeProjectionOpenIso_inv_inclusion :
    (nativeProjectionOpenIso X Z).inv ≫
        (nativeLineFunctor.map (nativeOpenBaseInclusion X Z)).hom =
      ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι :=
  (nativeMap_isPullback (nativeOpenBaseInclusion X Z)).isoIsPullback_inv_fst _ _ _

end AlgebraicGeometry.Scheme.ProjectiveLine
