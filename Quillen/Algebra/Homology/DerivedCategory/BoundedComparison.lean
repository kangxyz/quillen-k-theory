/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.Triangulated.HomComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Bounded derived comparison by finite canonical truncations

Canonical truncation triangles generate each cohomologically bounded object
from single objects. A refined version retains any isomorphism-invariant
property of homology containing zero, using the actual homology maps of both
truncations. Bijectivity of a triangulated functor's original Hom map on
shifted singles therefore implies bijectivity on all bounded objects.
Exact functors preserve these bounds; faithful exact functors reflect them.
All degree bounds are explicit. No boundedness of chosen complex terms is
assumed in the generation or Hom-comparison criteria.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace Quillen.DerivedHomComparison
variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

instance mapDerivedCategory_isGE (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    (F.mapDerivedCategory.obj K).IsGE n := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isGE n
  exact ⟨(F.mapHomologicalComplex (.up ℤ)).obj L,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app L, inferInstance⟩

instance mapDerivedCategory_isLE (K : DerivedCategory C) (n : ℤ) [K.IsLE n] :
    (F.mapDerivedCategory.obj K).IsLE n := by
  obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE n
  exact ⟨(F.mapHomologicalComplex (.up ℤ)).obj L,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app L, inferInstance⟩


def mapDerivedCategoryHomologyIso (K : DerivedCategory C) (i : ℤ) :
    (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj K) := by
  let Q := DerivedCategory.Q (C := C)
  let L := Q.objPreimage K
  let e := Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor D i).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso (F.mapDerivedCategoryFactors.app L) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≪≫
    (L.sc i).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C i).symm.app L ≪≫
      (DerivedCategory.homologyFunctor C i).mapIso e)

lemma mapDerivedCategory_homology_isZero_iff [F.Faithful] (K : DerivedCategory C) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  rw [(mapDerivedCategoryHomologyIso F K i).isZero_iff]
  refine ⟨fun h => ?_, fun h => F.map_isZero h⟩
  rw [IsZero.iff_id_eq_zero]
  apply F.map_injective
  exact h.eq_of_src _ _

lemma mapDerivedCategory_isGE_iff [F.Faithful] (K : DerivedCategory C) (n : ℤ) :
    (F.mapDerivedCategory.obj K).IsGE n ↔ K.IsGE n := by
  simp only [DerivedCategory.isGE_iff, mapDerivedCategory_homology_isZero_iff]

lemma mapDerivedCategory_isLE_iff [F.Faithful] (K : DerivedCategory C) (n : ℤ) :
    (F.mapDerivedCategory.obj K).IsLE n ↔ K.IsLE n := by
  simp only [DerivedCategory.isLE_iff, mapDerivedCategory_homology_isZero_iff]

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

lemma property_of_bounded_single_generation
    (P : ObjectProperty (DerivedCategory C)) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₂]
    (hsingle : ∀ (X : C) (n : ℤ), P ((DerivedCategory.singleFunctor C n).obj X))
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b] : P K := by
  have H : ∀ (n : ℕ) (a : ℤ) (K : DerivedCategory C),
      K.IsGE a → K.IsLE (a + n) → P K := by
    intro n
    induction n with
    | zero =>
      intro a K hge hle
      have : K.IsLE a := by simpa using hle
      obtain ⟨X, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K a
      exact P.prop_of_iso e.symm (hsingle X a)
    | succ n ih =>
      intro a K hge hle
      let t := DerivedCategory.TStructure.t (C := C)
      have : K.IsLE (a + n + 1) := by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hle
      let A := (t.truncLE (a + n)).obj K
      let B := (t.truncGT (a + n)).obj K
      have hA : P A := ih a A inferInstance inferInstance
      have hB : P B := by
        obtain ⟨X, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE B (a + n + 1)
        exact P.prop_of_iso e.symm (hsingle X (a + n + 1))
      exact P.ext_of_isTriangulatedClosed₂ _ (t.triangleLEGT_distinguished (a + n) K) hA hB
  have hle : K.IsLE (a + (b - a).toNat) :=
    DerivedCategory.TStructure.t.isLE_of_le K b _ (by omega)
  exact H (b - a).toNat a K inferInstance hle

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

lemma isIso_homology_truncLE_ι (K : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGT n).obj K
  have hT := t.triangleLEGT_distinguished n K
  have : T.obj₃.IsGE (n+1) := inferInstanceAs (((t.truncGT n).obj K).IsGE (n+1))
  have hzero (j : ℤ) (hj : j ≤ n) : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ (n+1) j (by omega)
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
      ((hzero i hi).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i-1) i (by omega)).mpr
      ((hzero (i-1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₁)

lemma isIso_homology_truncGT_π (K : DerivedCategory C) (n i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGTπ n).app K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGT n).obj K
  have hT := t.triangleLEGT_distinguished n K
  have : T.obj₁.IsLE n := inferInstanceAs (((t.truncLE n).obj K).IsLE n)
  have hzero (j : ℤ) (hj : n < j) : IsZero ((DerivedCategory.homologyFunctor C j).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE T.obj₁ n j hj
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i+1) rfl).mpr
      ((hzero (i+1) (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
      ((hzero i hi).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C i).map T.mor₂)

lemma homology_property_truncLE (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (hzero : Q 0) (K : DerivedCategory C)
    (hK : ∀ i, Q ((DerivedCategory.homologyFunctor C i).obj K)) (n i : ℤ) :
    Q ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.TStructure.t.truncLE n).obj K)) := by
  by_cases hi : i ≤ n
  · have := isIso_homology_truncLE_ι K n i hi
    exact Q.prop_of_iso (asIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K))).symm (hK i)
  · have hz := DerivedCategory.isZero_of_isLE
      ((DerivedCategory.TStructure.t.truncLE n).obj K) n i (by omega)
    exact Q.prop_of_iso hz.isoZero.symm hzero

lemma homology_property_truncGT (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (hzero : Q 0) (K : DerivedCategory C)
    (hK : ∀ i, Q ((DerivedCategory.homologyFunctor C i).obj K)) (n i : ℤ) :
    Q ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.TStructure.t.truncGT n).obj K)) := by
  by_cases hi : n < i
  · have := isIso_homology_truncGT_π K n i hi
    exact Q.prop_of_iso (asIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGTπ n).app K))) (hK i)
  · have hz := DerivedCategory.isZero_of_isGE
      ((DerivedCategory.TStructure.t.truncGT n).obj K) (n+1) i (by omega)
    exact Q.prop_of_iso hz.isoZero.symm hzero

lemma property_of_bounded_homology_single_generation
    (P : ObjectProperty (DerivedCategory C)) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulatedClosed₂]
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms] (hzero : Q 0)
    (hsingle : ∀ (X : C), Q X → ∀ (n : ℤ), P ((DerivedCategory.singleFunctor C n).obj X))
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ i, Q ((DerivedCategory.homologyFunctor C i).obj K)) : P K := by
  have H₀ (K : DerivedCategory C) (n : ℤ) [K.IsGE n] [K.IsLE n]
      (hK : Q ((DerivedCategory.homologyFunctor C n).obj K)) : P K := by
    obtain ⟨X, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
    have hX : Q X := Q.prop_of_iso
      ((DerivedCategory.homologyFunctor C n).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app X) hK
    exact P.prop_of_iso e.symm (hsingle X hX n)
  have H : ∀ (n : ℕ) (a : ℤ) (K : DerivedCategory C),
      K.IsGE a → K.IsLE (a+n) →
      (∀ i, Q ((DerivedCategory.homologyFunctor C i).obj K)) → P K := by
    intro n
    induction n with
    | zero =>
      intro a K hge hle hK
      have : K.IsLE a := by simpa using hle
      exact H₀ K a (hK a)
    | succ n ih =>
      intro a K hge hle hK
      let t := DerivedCategory.TStructure.t (C := C)
      have : K.IsLE (a+n+1) := by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hle
      let A := (t.truncLE (a+n)).obj K
      let B := (t.truncGT (a+n)).obj K
      have hA : P A := ih a A inferInstance inferInstance (homology_property_truncLE Q hzero K hK _)
      have hB : P B := H₀ B (a+n+1) (homology_property_truncGT Q hzero K hK _ _)
      exact P.ext_of_isTriangulatedClosed₂ _ (t.triangleLEGT_distinguished (a+n) K) hA hB
  have hle : K.IsLE (a + (b-a).toNat) :=
    DerivedCategory.TStructure.t.isLE_of_le K b _ (by omega)
  exact H (b-a).toNat a K inferInstance hle hK

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : DerivedCategory C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [F.Additive] [F.IsTriangulated] in
lemma single_map_bijective_of_single_zero_shift
    (h : ∀ (X Y : C) (n : ℤ), Function.Bijective (F.map :
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) → _))
    (X Y : C) (i j : ℤ) :
    Function.Bijective (F.map : ((DerivedCategory.singleFunctor C i).obj X ⟶
      (DerivedCategory.singleFunctor C j).obj Y) → _) := by
  let eX := ((DerivedCategory.singleFunctors C).shiftIso (-i) i 0 (by simp)).app X
  let eY := ((shiftFunctorAdd' (DerivedCategory C) (i-j) (-i) (-j) (by omega)).app
      ((DerivedCategory.singleFunctor C 0).obj Y)).symm ≪≫
    ((DerivedCategory.singleFunctors C).shiftIso (-j) j 0 (by simp)).app Y
  exact map_bijective_of_iso F eX eY (map_bijective_shift F (h X Y (i-j)) (-i))

lemma single_bounded_map_bijective
    (h : ∀ (X Y : C) (n : ℤ), Function.Bijective (F.map :
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) → _))
    (X : C) (i : ℤ) (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b] :
    Function.Bijective (F.map : ((DerivedCategory.singleFunctor C i).obj X ⟶ K) → _) := by
  have H : rightHomComparison F ((DerivedCategory.singleFunctor C i).obj X) K := by
    apply property_of_bounded_single_generation _ _ K a b
    intro Y j n
    exact map_bijective_of_iso F (Iso.refl _)
      (((DerivedCategory.singleFunctors C).shiftIso n (j-n) j (by omega)).app Y).symm
      (single_map_bijective_of_single_zero_shift F h X Y i (j-n))
  exact map_bijective_of_iso F (Iso.refl _) ((shiftFunctorZero _ ℤ).app K) (H 0)

end Quillen.DerivedHomComparison

namespace Quillen.DerivedHomComparison
variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : DerivedCategory C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

lemma bounded_map_bijective_of_single_zero_shift
    (h : ∀ (X Y : C) (n : ℤ), Function.Bijective (F.map :
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) → _))
    (K L : DerivedCategory C) (a b c d : ℤ)
    [K.IsGE a] [K.IsLE b] [L.IsGE c] [L.IsLE d] :
    Function.Bijective (F.map : (K ⟶ L) → _) := by
  have H : leftHomComparison F L K := by
    apply property_of_bounded_single_generation _ _ K a b
    intro X i n
    exact map_bijective_of_iso F
      (((DerivedCategory.singleFunctors C).shiftIso n (i-n) i (by omega)).app X).symm
      (Iso.refl L) (single_bounded_map_bijective F h X (i-n) L c d)
  exact map_bijective_of_iso F ((shiftFunctorZero _ ℤ).app K) (Iso.refl L) (H 0)

end Quillen.DerivedHomComparison
