/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Perfect-complex Mayer–Vietoris consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.PerfectMayerVietoris
open Quillen.PerfectComplexes.PerfectMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] in
/-- The actual overlap difference retains the order and inverse sign. -/
theorem actual_difference_sign (n : ℕ) (x : PerfectK T.toScheme n) (y : PerfectK V n) :
    overlapDifference j T n (x,y) =
      perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) n x *
        (perfectKRestrict (j ⁻¹ᵁ T).ι n y)⁻¹ := rfl

omit [CompactSpace X] in
/-- The whole boundary recovers the old original relative connecting homomorphism. -/
theorem original_relative_boundary (n : ℕ) :
    (qcqsConnectingHom j T hT hcover n).comp (perfectOpenKRestrict (j ⁻¹ᵁ T).ι (n+1)) =
      (perfectSupportedKMap T.ι n).comp
        ((perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
          (perfectOpenConnectingHom (j ⁻¹ᵁ T).ι n)) := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  change ((perfectSupportedKMap T.ι n).comp
      ((perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
        (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n))).comp
      (perfectOpenKRestrict (j ⁻¹ᵁ T).ι (n+1)) = _
  rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, qcqsPerfectConnectingHom_comp_relative]

include hT hcover in
/-- Matching positive local classes have a genuine original global K-class lift. -/
theorem positive_matching_classes_glue (n : ℕ)
    (x : PerfectK T.toScheme (n+1)) (y : PerfectK V (n+1))
    (hxy : perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1) x =
      perfectKRestrict (j ⁻¹ᵁ T).ι (n+1) y) :
    ∃ z : PerfectK X (n+1), perfectKRestrict T.ι (n+1) z = x ∧
      perfectKRestrict j (n+1) z = y := by
  have hx : (x,y) ∈ (overlapDifference j T (n+1)).ker :=
    (Quillen.GroupMayerVietoris.mem_difference_ker _ _ (x,y)).mpr hxy
  rw [← (qcqs_positiveExactSequence j T hT hcover n).1] at hx
  obtain ⟨z,hz⟩ := hx
  exact ⟨z,congrArg Prod.fst hz,congrArg Prod.snd hz⟩

/-- Even at K-zero, two original global classes with the same restrictions
differ by an actual incoming overlap boundary. -/
theorem zero_global_classes_difference (a b : PerfectK X 0)
    (hT' : perfectKRestrict T.ι 0 a = perfectKRestrict T.ι 0 b)
    (hj : perfectKRestrict j 0 a = perfectKRestrict j 0 b) :
    ∃ x : PerfectK (j ⁻¹ᵁ T).toScheme 1,
      qcqsConnectingHom j T hT hcover 0 x = a * b⁻¹ := by
  have hm : a * b⁻¹ ∈ (restrictionPair j T 0).ker := by
    change (perfectKRestrict T.ι 0 (a * b⁻¹),perfectKRestrict j 0 (a * b⁻¹)) = (1,1)
    simp only [map_mul,map_inv,hT',hj,mul_inv_cancel]
  rw [← (qcqs_zeroTail j T hT hcover).2] at hm
  exact hm

/-- Both consecutive original restriction homomorphisms annihilate the actual boundary. -/
theorem original_boundary_restrictions (n : ℕ) :
    (perfectKRestrict T.ι n).comp (qcqsConnectingHom j T hT hcover n) = 1 ∧
    (perfectKRestrict j n).comp (qcqsConnectingHom j T hT hcover n) = 1 := by
  have hh (x : PerfectK (j ⁻¹ᵁ T).toScheme (n+1)) :
      (perfectKRestrict T.ι n (qcqsConnectingHom j T hT hcover n x),
        perfectKRestrict j n (qcqsConnectingHom j T hT hcover n x)) = (1,1) := by
    have hm : qcqsConnectingHom j T hT hcover n x ∈
        (qcqsConnectingHom j T hT hcover n).range := ⟨x,rfl⟩
    rw [(qcqs_positiveExactSequence j T hT hcover n).2.2] at hm
    exact hm
  constructor
  · ext x
    exact congrArg Prod.fst (hh x)
  · ext x
    exact congrArg Prod.snd (hh x)

/-- A zero incoming boundary is exactly a difference of two original local classes. -/
theorem zero_boundary_is_difference (n : ℕ) (x : PerfectK (j ⁻¹ᵁ T).toScheme (n+1)) :
    qcqsConnectingHom j T hT hcover n x = 1 ↔
      ∃ (a : PerfectK T.toScheme (n+1)) (b : PerfectK V (n+1)),
        perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1) a *
          (perfectKRestrict (j ⁻¹ᵁ T).ι (n+1) b)⁻¹ = x := by
  change x ∈ (qcqsConnectingHom j T hT hcover n).ker ↔ _
  rw [← (qcqs_positiveExactSequence j T hT hcover n).2.1]
  constructor
  · rintro ⟨⟨a,b⟩,hab⟩
    exact ⟨a,b,hab⟩
  · rintro ⟨a,b,hab⟩
    exact ⟨(a,b),hab⟩

end QuillenTest.PerfectMayerVietoris

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace QuillenTest.PerfectMayerVietorisKZero
open Quillen.PerfectComplexes.PerfectMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

include hT hcover in
/-- Matching original local K-zero classes genuinely glue, including degree zero. -/
theorem original_zero_pair_lift (x : PerfectK T.toScheme 0) (y : PerfectK V 0)
    (hxy : perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) 0 x =
      perfectKRestrict (j ⁻¹ᵁ T).ι 0 y) :
    ∃ z : PerfectK X 0, perfectKRestrict T.ι 0 z = x ∧ perfectKRestrict j 0 z = y :=
  qcqs_matching_zero_classes_glue j T hT hcover x y hxy

include hT hcover in
/-- The actual original local-pair position is exact in every connective degree. -/
theorem all_degree_pair_exact (n : ℕ) :
    (restrictionPair j T n).range = (overlapDifference j T n).ker := by
  cases n with
  | zero => exact qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T hT hcover
  | succ n => exact (qcqs_positiveExactSequence j T hT hcover n).1

/-- The top chart edge case retains both old restriction maps and a real global class. -/
theorem top_chart_zero_pair (x : PerfectK (⊤ : X.Opens).toScheme 0) (y : PerfectK V 0)
    (hxy : perfectKRestrict (j.resLE ⊤ (j ⁻¹ᵁ ⊤) le_rfl) 0 x =
      perfectKRestrict (j ⁻¹ᵁ ⊤).ι 0 y) :
    ∃ z : PerfectK X 0, perfectKRestrict (⊤ : X.Opens).ι 0 z = x ∧ perfectKRestrict j 0 z = y :=
  qcqs_matching_zero_classes_glue j ⊤ isCompact_univ (fun _ ↦ Or.inr trivial) x y hxy

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] in
include hcover in
/-- The geometry behind the K-zero obstruction uses an actual original
isomorphism on the overlap and returns a genuine original derived extension. -/
theorem specified_overlap_extension (E : CochainComplex T.toScheme.Modules ℤ)
    (B : CochainComplex V.Modules ℤ)
    (hE : locallyPerfect T.toScheme E) (hB : locallyPerfect V B)
    (e : (DerivedCategory.Q (C := (j ⁻¹ᵁ T).toScheme.Modules)).obj ((restrict (j ⁻¹ᵁ T).ι).obj B) ≅
      (DerivedCategory.Q (C := (j ⁻¹ᵁ T).toScheme.Modules)).obj
        ((restrict (j.resLE T (j ⁻¹ᵁ T) le_rfl)).obj E)) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      Nonempty ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj P) ≅
        (DerivedCategory.Q (C := T.toScheme.Modules)).obj E) :=
  (OpenDerivedImage.complexObjects_cover_iff j T hcover E hE).mpr ⟨B,hB,⟨e⟩⟩

end QuillenTest.PerfectMayerVietorisKZero
