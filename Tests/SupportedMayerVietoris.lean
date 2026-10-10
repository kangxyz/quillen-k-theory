/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.MayerVietoris

/-! # Supported Mayer–Vietoris consumers -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Tests.SupportedMayerVietoris
open Quillen.PerfectComplexes Quillen.PerfectComplexes.SupportedMayerVietoris
local instance (Y : Scheme.{u}) (A : Y.Opens) (n : ℕ) : CommGroup (PerfectSupportedK A.ι n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen A.ι) n
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hT : IsCompact (T : Set X)) (hZ : IsCompact (Z : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] in
/-- Actual supported overlap maps retain their first-minus-second sign. -/
theorem original_difference_sign (n : ℕ)
    (x : PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι n) (y : PerfectSupportedK (j ⁻¹ᵁ Z).ι n) :
    overlapDifference j T Z n (x,y) =
      SupportedOpenDerivedImage.overlapKRestrict j T Z n x *
        (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n y)⁻¹ := rfl

/-- The all-degree boundary recovers the unchanged supported relative map. -/
theorem original_relative_boundary (n : ℕ) :
    (qcqsConnectingHom j T Z hT hZ hcover n).comp
      (perfectSupportedOpenKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (n+1)) =
    (perfectSupportedUnionKMap T.ι Z n).comp
      ((qcqsFiberEquiv j T Z hT hcover n).symm.toMonoidHom.comp
        (perfectSupportedOpenConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n)) :=
  qcqsConnectingHom_comp_relative j T Z hT hZ hcover n

/-- The actual old public fiber map cancels its genuine inverse in degree zero. -/
theorem original_fiber_inverse (x : PerfectSupportedK (Z ⊔ T.ι.opensRange).ι 0) :
    (qcqsFiberEquiv j T Z hT hcover 0).symm
      (perfectSupportedKPullback (qcSupportedBaseSquare (fiberPair j T Z)) 0 x) = x :=
  (qcqsFiberEquiv j T Z hT hcover 0).symm_apply_apply x

include hT hZ hcover in
/-- Matching original K-zero classes retain a genuine globally supported lift. -/
theorem original_zero_pair_lift
    (x : PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι 0) (y : PerfectSupportedK (j ⁻¹ᵁ Z).ι 0)
    (hxy : SupportedOpenDerivedImage.overlapKRestrict j T Z 0 x =
      perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) 0 y) :
    ∃ z : PerfectSupportedK Z.ι 0,
      perfectSupportedKRestrict T.ι Z 0 z = x ∧ perfectSupportedKRestrict j Z 0 z = y :=
  qcqs_matching_classes_glue j T Z hT hZ hcover 0 x y hxy

include hT hZ hcover in
/-- The final supported pair position is exact in every connective degree. -/
theorem all_degree_pair_exact (n : ℕ) :
    (restrictionPair j T Z n).range = (overlapDifference j T Z n).ker := by
  cases n with
  | zero => exact qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T Z hT hZ hcover
  | succ n => exact (qcqs_positiveExactSequence j T Z hT hZ hcover n).1

/-- Two original global supported K-zero lifts differ by the genuine incoming boundary. -/
theorem zero_global_classes_difference (a b : PerfectSupportedK Z.ι 0)
    (ha : perfectSupportedKRestrict T.ι Z 0 a = perfectSupportedKRestrict T.ι Z 0 b)
    (hb : perfectSupportedKRestrict j Z 0 a = perfectSupportedKRestrict j Z 0 b) :
    ∃ x : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι 1,
      qcqsConnectingHom j T Z hT hZ hcover 0 x = a * b⁻¹ := by
  have hm : a * b⁻¹ ∈ (restrictionPair j T Z 0).ker := by
    change (perfectSupportedKRestrict T.ι Z 0 (a*b⁻¹),perfectSupportedKRestrict j Z 0 (a*b⁻¹)) =
      (1,1)
    simp only [map_mul,map_inv,ha,hb,mul_inv_cancel]
  rw [← (qcqs_completeZeroTail j T Z hT hZ hcover).2.1] at hm
  exact hm

/-- Both original restrictions kill the actual whole boundary homomorphism. -/
theorem original_boundary_restrictions (n : ℕ) :
    (perfectSupportedKRestrict T.ι Z n).comp (qcqsConnectingHom j T Z hT hZ hcover n) = 1 ∧
    (perfectSupportedKRestrict j Z n).comp (qcqsConnectingHom j T Z hT hZ hcover n) = 1 := by
  have hh (x : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1)) :
      (perfectSupportedKRestrict T.ι Z n (qcqsConnectingHom j T Z hT hZ hcover n x),
        perfectSupportedKRestrict j Z n (qcqsConnectingHom j T Z hT hZ hcover n x)) = (1,1) := by
    have hm : qcqsConnectingHom j T Z hT hZ hcover n x ∈
        (qcqsConnectingHom j T Z hT hZ hcover n).range := ⟨x,rfl⟩
    rw [(qcqs_positiveExactSequence j T Z hT hZ hcover n).2.2] at hm
    exact hm
  constructor
  · ext x; exact congrArg Prod.fst (hh x)
  · ext x; exact congrArg Prod.snd (hh x)

include hT hZ hcover in
/-- Original K-zero image reflection uses the literal supported restriction. -/
theorem sharp_original_image (x : PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι 0) :
    (∃ y, perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) 0 y =
      SupportedOpenDerivedImage.overlapKRestrict j T Z 0 x) ↔
    ∃ z, perfectSupportedKRestrict T.ι Z 0 z = x :=
  SupportedOpenDerivedImage.restrict_mem_range_iff_of_cover j T Z hT hZ hcover x

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] in
include hcover in
/-- The geometric input returns a genuine perfect complex vanishing on the
prescribed auxiliary open from a specified actual overlap isomorphism. -/
theorem specified_supported_overlap_extension (E : Complex T.toScheme) (B : Complex V)
    (hE : perfectSupported (T.ι ⁻¹ᵁ Z).ι E) (hB : perfectSupported (j ⁻¹ᵁ Z).ι B)
    (e : (toDerived (j ⁻¹ᵁ T).toScheme).obj ((restrict (j ⁻¹ᵁ T).ι).obj B) ≅
      (toDerived (j ⁻¹ᵁ T).toScheme).obj ((restrict (j.resLE T (j ⁻¹ᵁ T) le_rfl)).obj E)) :
    ∃ P : Complex X, perfectSupported Z.ι P ∧
      Nonempty ((toDerived T.toScheme).obj ((restrict T.ι).obj P) ≅ (toDerived T.toScheme).obj E) :=
  (SupportedOpenDerivedImage.complexObjects_cover_iff j T Z hcover E hE).mpr ⟨B,hB,⟨e⟩⟩

include hT hcover in
/-- The globally acyclic auxiliary-support edge case retains the same original maps. -/
theorem top_support_pair_lift
    (x : PerfectSupportedK (T.ι ⁻¹ᵁ (⊤ : X.Opens)).ι 0)
    (y : PerfectSupportedK (j ⁻¹ᵁ (⊤ : X.Opens)).ι 0)
    (hxy : SupportedOpenDerivedImage.overlapKRestrict j T ⊤ 0 x =
      perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ (⊤ : X.Opens)) 0 y) :
    ∃ z : PerfectSupportedK (⊤ : X.Opens).ι 0,
      perfectSupportedKRestrict T.ι ⊤ 0 z = x ∧ perfectSupportedKRestrict j ⊤ 0 z = y :=
  qcqs_matching_classes_glue j T ⊤ hT isCompact_univ hcover 0 x y hxy

end Tests.SupportedMayerVietoris
