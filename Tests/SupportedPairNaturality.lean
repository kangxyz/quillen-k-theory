/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.AuxiliaryNaturality

/-! # Supported pair naturality consumers -/
@[expose] public section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Quillen.PerfectComplexes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Quillen.Tests.SupportedPairNaturality

section Relative
variable {U' X' U X : Scheme.{u}}
variable (j' : U' ⟶ X') (j : U ⟶ X)
variable [IsOpenImmersion j'] [IsOpenImmersion j]
variable {S : X'.Opens} {T : X.Opens}
variable (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
variable (w : j' ≫ f.hom.right = g ≫ j)
include g w in
/-- The actual original chain restriction of the actual pullback is weak. -/
lemma original_boundedFlat_relative_quasiIso
    {K L : (boundedFlatPerfectSupported T.ι).FullSubcategory} (p : K ⟶ L)
    (hp : QuasiIso ((restrict j).map p.hom)) :
    QuasiIso ((restrict j').map ((pullbackComplex f.hom.right).map p.hom)) := by
  exact @boundedFlatPerfect_pairPullback_quasiIso _ _
    (supportedOpenRestrictionSquare j' j f g w) _ _ K.property.1 L.property.1 p.hom hp

variable [CompactSpace X'] [CompactSpace X]

/-- whole original relative degree-zero boundary. -/
lemma original_relative_boundary_square :
    (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) 0).comp
        (perfectSupportedOpenConnectingHom j T 0) =
    (perfectSupportedOpenConnectingHom j' S 0).comp
      (perfectSupportedOpenKPullback j' j f g w 1) := by
  exact perfectSupportedOpenConnectingHom_pullback j' j f g w 0

variable [CompactSpace U'] [CompactSpace U]

/-- original public K0 restriction square. -/
lemma original_relative_KZero_restriction :
    (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) 0).comp
        (perfectSupportedOpenKRestrict j T 0) =
    (perfectSupportedOpenKRestrict j' S 0).comp
      (perfectSupportedOpenKPullback j' j f g w 0) := by
  exact perfectSupportedOpenKRestrict_pullback j' j f g w 0

variable [QuasiSeparatedSpace X'] [QuasiSeparatedSpace X]
variable (hS : IsCompact (S : Set X')) (hT : IsCompact (T : Set X))

/-- original target K1-to-K0 boundary homomorphism. -/
lemma original_target_KZero_boundary :
    (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) 0).comp
        (qcqsPerfectSupportedConnectingHom j T hT 0) =
    (qcqsPerfectSupportedConnectingHom j' S hS 0).comp
      (perfectSupportedKPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) 1) := by
  exact qcqsPerfectSupportedConnectingHom_pullback j' j f g w hS hT 0

/-- actual positive inverse under arbitrary squares. -/
lemma original_positive_inverse (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) :
    perfectSupportedOpenKPullback j' j f g w (n+1)
      ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
    (qcqsPerfectSupportedOpenKEquiv j' S hS n).symm
      (perfectSupportedKPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) (n+1) x) := by
  exact qcqsPerfectSupportedOpenKEquiv_symm_pullback j' j f g w hS hT n x

/-- all three actual homomorphism squares at the tail. -/
lemma original_zero_tail_three_squares :
    ((perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) 0).comp
        (qcqsPerfectSupportedConnectingHom j T hT 0) =
      (qcqsPerfectSupportedConnectingHom j' S hS 0).comp
        (perfectSupportedKPullback
          (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) 1)) ∧
    ((perfectSupportedKPullback (qcSupportedBaseSquare f) 0).comp
        (perfectSupportedUnionKMap j T 0) =
      (perfectSupportedUnionKMap j' S 0).comp
        (perfectSupportedKPullback
          (qcSupportedBaseSquare (supportedPairUnionSquare j' j f g w)) 0)) ∧
    ((perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare j' j f g w)) 0).comp
        (perfectSupportedKRestrict j T 0) =
      (perfectSupportedKRestrict j' S 0).comp
        (perfectSupportedKPullback (qcSupportedBaseSquare f) 0)) := by
  exact ⟨qcqsPerfectSupportedConnectingHom_pullback j' j f g w hS hT 0,
    perfectSupportedUnionKMap_pullback j' j f g w 0,
    perfectSupportedKRestrict_pairPullback j' j f g w 0⟩
end Relative

section Identity
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (T : X.Opens) [CompactSpace X]

/-- the original relative K0 identity. -/
lemma original_relative_KZero_identity :
    perfectSupportedOpenKPullback j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) 0 = MonoidHom.id _ := by
  exact perfectSupportedOpenKPullback_id j T 0
end Identity

/- A genuinely noncartesian identity-base support square. -/
private lemma support_square_noncartesian
    {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T)
    (x : X) (hxT : x ∈ T) (hxS : x ∉ S) :
    ¬ IsPullback (X.homOfLE h) S.ι T.ι (𝟙 X) := by
  intro hp
  have : IsIso (X.homOfLE h) := hp.isIso_fst_of_isIso
  obtain ⟨y, hy⟩ := (X.homOfLE h).surjective ⟨x, hxT⟩
  have hv := congrArg Subtype.val hy
  change (X.homOfLE h y).val = x at hv
  rw [Scheme.homOfLE_apply] at hv
  exact hxS (hv ▸ y.property)

/-- Two genuinely noncartesian support squares still compose on original K. -/
lemma original_noncartesian_relative_composition
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace X]
    {R S T : X.Opens} (hRS : R ≤ S) (hST : S ≤ T)
    (x y : X) (hxT : x ∈ T) (hxS : x ∉ S) (hyS : y ∈ S) (hyR : y ∉ R)
    (n : ℕ) :
    (¬ IsPullback (X.homOfLE hST) S.ι T.ι (𝟙 X)) ∧
    (¬ IsPullback (X.homOfLE hRS) R.ι S.ι (𝟙 X)) ∧
    perfectSupportedOpenKPullback j j
      (supportChangeOpenPair (hRS.trans hST)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n =
    (perfectSupportedOpenKPullback j j (supportChangeOpenPair hRS) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n).comp
    (perfectSupportedOpenKPullback j j (supportChangeOpenPair hST) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n) := by
  refine ⟨support_square_noncartesian hST x hxT hxS,
    support_square_noncartesian hRS y hyS hyR, ?_⟩
  have he : supportChangeOpenPair hRS ≫ supportChangeOpenPair hST =
      supportChangeOpenPair (hRS.trans hST) := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · change X.homOfLE hRS ≫ X.homOfLE hST = X.homOfLE (hRS.trans hST)
      exact Scheme.homOfLE_homOfLE X hRS hST
    · change (𝟙 X : X ⟶ X) ≫ 𝟙 X = 𝟙 X
      exact Category.id_comp _
  simpa only [he, Category.id_comp] using
    perfectSupportedOpenKPullback_comp j j (supportChangeOpenPair hST) (𝟙 U)
    (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) j (supportChangeOpenPair hRS) (𝟙 U)
    (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n

end Quillen.Tests.SupportedPairNaturality
