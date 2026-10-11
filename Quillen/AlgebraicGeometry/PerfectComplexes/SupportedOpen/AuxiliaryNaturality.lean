/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalLocalization
public import Quillen.Waldhausen.Fibration.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison

/-!
# Original auxiliary-support naturality

An inclusion S ≤ T of acyclicity opens gives literal inclusions of the existing
supported perfect categories. The actual fine, relative and union-fiber maps
commute with change of weak equivalences, restriction, and the original
relative boundary without compactness hypotheses. Source inclusion K-maps
satisfy identity and composition.

For compact X these inclusions are precisely the existing public supported
pair pullbacks on the actual identity-base squares. For qcqs X, compact U and
compact S,T, the original target supported boundary and the positive inverse
endpoint are natural under the same original inclusions. The theorem concerns
variation of auxiliary support on a fixed base and localization open.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
attribute [local instance] HasDerivedCategory.standard

/-- Shrinking the acyclicity open weakens the original support predicate. -/
lemma perfectSupported_antitone {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T) :
    perfectSupported T.ι ≤ perfectSupported S.ι := by
  intro K hK
  refine ⟨hK.1, ?_⟩
  rw [← isZero_toDerived_iff_acyclic]
  let c : restrict T.ι ⋙ restrict (X.homOfLE h) ≅ restrict S.ι :=
    restrictCompIso _ _ ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X h))
  exact (isZero_toDerived_restrict_of_isZero (X.homOfLE h)
    ((isZero_toDerived_iff_acyclic _).mpr hK.2)).of_iso
      ((toDerived S.toScheme).mapIso (c.app K)).symm

/-- The original supported inclusion, with only the acyclicity open weakened. -/
def perfectSupportedChangeOpenKMap {X : Scheme.{u}} {S T : X.Opens}
    (h : S ≤ T) (n : ℕ) : PerfectSupportedK T.ι n →* PerfectSupportedK S.ι n :=
  subcategoryKMap (perfectSupported T.ι) (perfectSupported S.ι) (perfectSupported_antitone h) n

@[simp] lemma perfectSupportedChangeOpenKMap_refl {X : Scheme.{u}} (T : X.Opens) (n : ℕ) :
    perfectSupportedChangeOpenKMap (le_refl T) n = MonoidHom.id _ := by
  unfold perfectSupportedChangeOpenKMap subcategoryKMap
  exact KMap_id (perfectSupportedWaldhausen T.ι) n

lemma perfectSupportedChangeOpenKMap_comp {X : Scheme.{u}} {R S T : X.Opens}
    (h : R ≤ S) (k : S ≤ T) (n : ℕ) :
    perfectSupportedChangeOpenKMap (h.trans k) n =
      (perfectSupportedChangeOpenKMap h n).comp (perfectSupportedChangeOpenKMap k n) := by
  unfold perfectSupportedChangeOpenKMap subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {S T : X.Opens} (h : S ≤ T)

lemma perfectSupportedOpenChangeOpen_exact : IsExact
    (perfectSupportedOpenWeakWaldhausen j T).cof (perfectSupportedOpenWeakWaldhausen j T).weq
    (perfectSupportedOpenWeakWaldhausen j S).cof (perfectSupportedOpenWeakWaldhausen j S).weq
    (ObjectProperty.ιOfLE (perfectSupported_antitone h)) where
  zero := (subcategoryInclusion_exact _ _ (perfectSupported_antitone h)).zero
  cofibration := (subcategoryInclusion_exact _ _ (perfectSupported_antitone h)).cofibration
  weak _ hf := hf
  pushout := (subcategoryInclusion_exact _ _ (perfectSupported_antitone h)).pushout

/-- The same literal inclusion on the relative weak categories. -/
def perfectSupportedOpenChangeOpenKMap (n : ℕ) :
    PerfectSupportedOpenK j T n →* PerfectSupportedOpenK j S n :=
  KMap (perfectSupportedOpenChangeOpen_exact j h) n

lemma perfectSupportedOpenChangeOpenKMap_comp_changeWeak (n : ℕ) :
    (perfectSupportedOpenChangeOpenKMap j h n).comp (perfectSupportedOpenKMap j T n) =
      (perfectSupportedOpenKMap j S n).comp (perfectSupportedChangeOpenKMap h n) := by
  unfold perfectSupportedOpenChangeOpenKMap perfectSupportedOpenKMap perfectSupportedChangeOpenKMap
    subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

lemma perfectSupportedOpenChangeOpenKMap_comp_restrict (n : ℕ) :
    (perfectSupportedOpenKRestrict j S n).comp (perfectSupportedOpenChangeOpenKMap j h n) =
      (perfectSupportedChangeOpenKMap (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx) n).comp
        (perfectSupportedOpenKRestrict j T n) := by
  unfold perfectSupportedOpenKRestrict perfectSupportedOpenChangeOpenKMap
    perfectSupportedChangeOpenKMap subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- The original absolute restriction square commutes on the supported groups. -/
lemma perfectSupportedChangeOpenKMap_comp_restrict (n : ℕ) :
    (perfectSupportedKRestrict j S n).comp (perfectSupportedChangeOpenKMap h n) =
      (perfectSupportedChangeOpenKMap (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx) n).comp
        (perfectSupportedKRestrict j T n) := by
  unfold perfectSupportedKRestrict perfectSupportedChangeOpenKMap subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- The original fiber-to-source square commutes on the actual union support. -/
lemma perfectSupportedChangeOpenKMap_comp_union (n : ℕ) :
    (perfectSupportedChangeOpenKMap h n).comp (perfectSupportedUnionKMap j T n) =
      (perfectSupportedUnionKMap j S n).comp
        (perfectSupportedChangeOpenKMap (sup_le_sup_right h j.opensRange) n) := by
  unfold perfectSupportedUnionKMap perfectSupportedChangeOpenKMap subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

lemma perfectSupportedUnionChangeOpenKMap_comp_flatten (n : ℕ) :
    (perfectSupportedChangeOpenKMap (sup_le_sup_right h j.opensRange) n).comp
        (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      (perfectSupportedOpenAcyclicSupportedKEquiv j S n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectSupportedOpenNested j
          S)
          (subcategoryInclusion_exact _ _ (perfectSupported_antitone h))
          (perfectSupportedOpenChangeOpen_exact j h)) n) := by
  change (KMap (subcategoryInclusion_exact _ _ (perfectSupported_antitone (sup_le_sup_right h
    j.opensRange))) n).comp
    (KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n) =
    (KMap (perfectSupportedOpenAcyclicToSupported_exact j S) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- The genuine relative boundary is natural under auxiliary support inclusion. -/
lemma perfectSupportedOpenConnectingHom_changeOpen (n : ℕ) :
    (perfectSupportedChangeOpenKMap (sup_le_sup_right h j.opensRange) n).comp
        (perfectSupportedOpenConnectingHom j T n) =
      (perfectSupportedOpenConnectingHom j S n).comp (perfectSupportedOpenChangeOpenKMap j h (n+1))
        := by
  unfold perfectSupportedOpenConnectingHom perfectSupportedOpenChangeOpenKMap
  rw [← MonoidHom.comp_assoc, perfectSupportedUnionChangeOpenKMap_comp_flatten j h n,
    MonoidHom.comp_assoc]
  rw [changeWeakConnectingHom_natural (perfectSupportedOpenNested j T) (perfectSupportedOpenNested j
    S)
    (subcategoryInclusion_exact _ _ (perfectSupported_antitone h))
    (perfectSupportedOpenChangeOpen_exact j h)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j S)]
  rw [MonoidHom.comp_assoc]

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (hS : IsCompact (S : Set X)) (hT : IsCompact (T : Set X))

/-- The actual target boundary is natural under the original supported inclusion. -/
theorem qcqsPerfectSupportedConnectingHom_changeOpen (n : ℕ) :
    (perfectSupportedChangeOpenKMap (sup_le_sup_right h j.opensRange) n).comp
        (qcqsPerfectSupportedConnectingHom j T hT n) =
      (qcqsPerfectSupportedConnectingHom j S hS n).comp
        (perfectSupportedChangeOpenKMap (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx) (n+1)) := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqs_perfectSupportedOpenKRestrict_succ_bijective j T hT n).surjective x
  have h₁ := DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative j T hT n) a
  have h₂ := DFunLike.congr_fun (perfectSupportedOpenConnectingHom_changeOpen j h n) a
  have h₃ := DFunLike.congr_fun (perfectSupportedOpenChangeOpenKMap_comp_restrict j h (n+1)) a
  have h₄ := DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative j S hS n)
    (perfectSupportedOpenChangeOpenKMap j h (n+1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, ← h₃, h₄]

/-- The original positive inverse respects actual auxiliary support inclusion. -/
theorem qcqsPerfectSupportedOpenKEquiv_symm_changeOpen (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenChangeOpenKMap j h (n+1)
        ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
      (qcqsPerfectSupportedOpenKEquiv j S hS n).symm
        (perfectSupportedChangeOpenKMap (show j ⁻¹ᵁ S ≤ j ⁻¹ᵁ T from fun _ hx => h hx) (n+1) x) :=
          by
  apply (qcqsPerfectSupportedOpenKEquiv j S hS n).injective
  change perfectSupportedOpenKRestrict j S (n+1)
    (perfectSupportedOpenChangeOpenKMap j h (n+1) ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm
      x)) = _
  have hs := DFunLike.congr_fun (perfectSupportedOpenChangeOpenKMap_comp_restrict j h (n+1))
    ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)
  simp only [MonoidHom.comp_apply] at hs
  rw [hs]
  change perfectSupportedChangeOpenKMap _ (n+1)
    (qcqsPerfectSupportedOpenKEquiv j T hT n ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T)

/-- The actual identity-base square for an inclusion of auxiliary opens. -/
def supportChangeOpenPair : supportOpenPair S ⟶ supportOpenPair T :=
  ObjectProperty.homMk (Arrow.homMk (X.homOfLE h) (𝟙 X)
    (by change X.homOfLE h ≫ T.ι = S.ι ≫ 𝟙 X
        rw [Category.comp_id, Scheme.homOfLE_ι]))

/-- Actual bounded-flat pullback on the identity base is the literal inclusion. -/
def boundedFlatPerfectSupportedChangeOpenIso :
    boundedFlatPerfectSupportedInclusion T.ι ⋙ ObjectProperty.ιOfLE (perfectSupported_antitone h) ≅
      boundedFlatPerfectSupportedPullback (supportChangeOpenPair h) ⋙
        boundedFlatPerfectSupportedInclusion S.ι :=
  Functor.fullyFaithfulCancelRight (perfectSupported S.ι).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported T.ι).ι (pullbackComplexIdIso X).symm)

lemma perfectSupportedChangeOpenKMap_comp_boundedFlat (n : ℕ) :
    (perfectSupportedChangeOpenKMap h n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap S.ι n).comp
        (boundedFlatPerfectSupportedKPullback (supportChangeOpenPair h) n) := by
  unfold perfectSupportedChangeOpenKMap Waldhausen.subcategoryKMap
    boundedFlatPerfectSupportedToPerfectSupportedKMap boundedFlatPerfectSupportedKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFlatPerfectSupportedChangeOpenIso h) n

variable [CompactSpace X]

/-- The actual auxiliary-support change as a morphism of quasi-compact open pairs. -/
def qcSupportChangeOpenPair :
    (⟨supportOpenPair S, (by change CompactSpace X; infer_instance)⟩ :
      Quillen.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk (supportChangeOpenPair h)

/-- Changing auxiliary support is precisely the existing public pair pullback. -/
lemma perfectSupportedChangeOpenKMap_eq_pullback (n : ℕ) :
    perfectSupportedChangeOpenKMap h n = perfectSupportedKPullback (qcSupportChangeOpenPair h) n :=
  perfectSupportedKPullback_unique (qcSupportChangeOpenPair h) n
    (perfectSupportedChangeOpenKMap h n) (perfectSupportedChangeOpenKMap_comp_boundedFlat h n)

end Quillen.PerfectComplexes

end
