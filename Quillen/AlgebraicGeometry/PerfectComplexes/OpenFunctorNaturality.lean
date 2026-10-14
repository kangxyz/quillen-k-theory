/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization
public import Quillen.Waldhausen.Fibration.ConnectingNaturality

/-! # Exact restriction squares and the original supported boundary

An exact functor compatible with the actual open restrictions preserves the
original relative weak equivalences and supported objects. The canonical
change-of-weak boundary gives the original qcqs connecting square in every
degree, including the boundary from K1 to supported K0.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenFunctorNaturality
open Waldhausen Fibration

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- An exact square of the original perfect functors and actual open restrictions. -/
structure ExactRestrictionSquare where
  ambient : Perfect X ⥤ Perfect Y
  onOpen : Perfect U ⥤ Perfect V
  ambient_exact : IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
    (perfectWaldhausen Y).cof (perfectWaldhausen Y).weq ambient
  onOpen_exact : IsExact (perfectWaldhausen U).cof (perfectWaldhausen U).weq
    (perfectWaldhausen V).cof (perfectWaldhausen V).weq onOpen
  restrictionIso : ambient ⋙ perfectRestrict k ≅ perfectRestrict j ⋙ onOpen

namespace ExactRestrictionSquare
variable {j k} (D : ExactRestrictionSquare j k)

/-- The original square preserves quasi-isomorphisms on the prescribed open. -/
theorem coarseExact : IsExact (perfectOpenWeakWaldhausen j).cof
    (perfectOpenWeakWaldhausen j).weq (perfectOpenWeakWaldhausen k).cof
    (perfectOpenWeakWaldhausen k).weq D.ambient where
  zero := D.ambient_exact.zero
  cofibration := D.ambient_exact.cofibration
  pushout := D.ambient_exact.pushout
  weak {A B} f hf := by
    have : QuasiIso ((locallyPerfect V).ι.map ((perfectRestrict j ⋙ D.onOpen).map f)) :=
      D.onOpen_exact.weak ((perfectRestrict j).map f) hf
    let e := Functor.isoWhiskerRight D.restrictionIso.symm (locallyPerfect V).ι
    exact quasiIso_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app A) (e.app B) (e.hom.naturality f).symm)

/-- The actual ambient functor restricted to supported complexes, retaining its chain objects. -/
def supported : (perfectSupported j).FullSubcategory ⥤ (perfectSupported k).FullSubcategory :=
  perfectSupportedToAcyclic j ⋙
    acyclicFunctor (perfectOpenNested j) (perfectOpenNested k) D.coarseExact ⋙
      perfectAcyclicToSupported k

/-- Supported restriction retains the original underlying complex. -/
@[simp] theorem supported_obj (K : (perfectSupported j).FullSubcategory) :
    (D.supported.obj K).obj = (D.ambient.obj ⟨K.obj, K.property.1⟩).obj := rfl

/-- Supported restriction retains the original underlying chain map. -/
@[simp] theorem supported_map {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (D.supported.map f).hom = (D.ambient.map ((locallyPerfect X).homMk f.hom)).hom := rfl

/-- Exactness uses the original fine classes and the proved supported/acyclic identification. -/
theorem supported_exact : IsExact (perfectSupportedWaldhausen j).cof
    (perfectSupportedWaldhausen j).weq (perfectSupportedWaldhausen k).cof
    (perfectSupportedWaldhausen k).weq D.supported :=
  (perfectSupportedToAcyclic_exact j).comp
    ((acyclicFunctor_exact (perfectOpenNested j) (perfectOpenNested k)
      D.ambient_exact D.coarseExact).comp (perfectAcyclicToSupported_exact k))

/-- The K-map of the actual supported functor. -/
def supportedKMap (n : ℕ) : PerfectSupportedK j n →* PerfectSupportedK k n :=
  KMap D.supported_exact n

/-- The K-map on the unchanged categories with their original localized weak classes. -/
def relativeKMap (n : ℕ) : PerfectOpenK j n →* PerfectOpenK k n :=
  KMap D.coarseExact n

/-- The actual supported map commutes with the original support-forgetting maps. -/
theorem supportedKMap_forget (n : ℕ) :
    (perfectSupportedKMap k n).comp (D.supportedKMap n) =
      (KMap D.ambient_exact n).comp (perfectSupportedKMap j n) := by
  unfold supportedKMap perfectSupportedKMap subcategoryKMap
  rw [KMap_comp_KMap, KMap_comp_KMap]

/-- Flattening the original acyclic categories commutes with the actual supported operator. -/
theorem supportedKMap_flatten (n : ℕ) :
    (D.supportedKMap n).comp (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      (perfectAcyclicSupportedKEquiv k n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectOpenNested j) (perfectOpenNested k)
          D.ambient_exact D.coarseExact) n) := by
  change (KMap D.supported_exact n).comp (KMap (perfectAcyclicToSupported_exact j) n) =
    (KMap (perfectAcyclicToSupported_exact k) n).comp _
  rw [KMap_comp_KMap, KMap_comp_KMap]

/-- The canonical original relative boundary is natural for the exact restriction square. -/
theorem relativeConnectingHom (n : ℕ) :
    (D.supportedKMap n).comp (perfectOpenConnectingHom j n) =
      (perfectOpenConnectingHom k n).comp (D.relativeKMap (n + 1)) := by
  unfold perfectOpenConnectingHom relativeKMap
  rw [← MonoidHom.comp_assoc, D.supportedKMap_flatten, MonoidHom.comp_assoc]
  rw [changeWeakConnectingHom_natural (perfectOpenNested j) (perfectOpenNested k)
    D.ambient_exact D.coarseExact
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence k)]
  rw [MonoidHom.comp_assoc]

/-- The relative endpoint square uses the given original restriction comparison. -/
theorem relativeKMap_restrict (n : ℕ) :
    (perfectOpenKRestrict k n).comp (D.relativeKMap n) =
      (KMap D.onOpen_exact n).comp (perfectOpenKRestrict j n) := by
  unfold perfectOpenKRestrict relativeKMap
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ D.restrictionIso n

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace V]

/-- The original qcqs boundary commutes with the actual supported functor, including K1 to K0. -/
theorem qcqsConnectingHom (n : ℕ) :
    (D.supportedKMap n).comp (qcqsPerfectConnectingHom j n) =
      (qcqsPerfectConnectingHom k n).comp (KMap D.onOpen_exact (n + 1)) := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqsPerfectOpenKEquiv j n).surjective x
  have h₁ := DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative j n) a
  have h₂ := DFunLike.congr_fun (D.relativeConnectingHom n) a
  have h₃ := DFunLike.congr_fun (D.relativeKMap_restrict (n + 1)) a
  have h₄ := DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative k n)
    (D.relativeKMap (n + 1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  change D.supportedKMap n
      (qcqsPerfectConnectingHom j n (perfectOpenKRestrict j (n + 1) a)) =
    qcqsPerfectConnectingHom k n
      (KMap D.onOpen_exact (n + 1) (perfectOpenKRestrict j (n + 1) a))
  rw [h₁, h₂, ← h₃, h₄]

end ExactRestrictionSquare
end Quillen.PerfectComplexes.OpenFunctorNaturality
