/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenLocalization
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenCoverExactness
public import Quillen.Algebra.Homology.ShortComplex.ProductSequence

/-!
# The original signed two-open Čech sheaf sequence

For a genuine cartesian square of open immersions covering the ambient scheme,
the original restriction units and signed restriction difference give a short
exact sequence of module sheaves. The proof uses explicit splitting on each
chart and exactness reflection on the actual cover. The sequence is functorial
in arbitrary original sheaf maps. No quasicoherence, flasqueness, affine, or
noetherian hypothesis is imposed on the sheaf. Derived base change is separate.
-/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
open CategoryTheory.ShortComplex

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k) (M : X.Modules)
/-- The original second restriction transported to the common actual overlap immersion. -/
def sheafSecondRestriction :
    (openLocalization k).obj M ⟶ (openLocalization (a ≫ j)).obj M :=
  openLocalizationMap b k M ≫ (openLocalizationCongr h.symm).hom.app M
/-- The pair of original open-restriction adjunction units. -/
def sheafAugmentation : M ⟶ (openLocalization j).obj M ⨯ (openLocalization k).obj M :=
  prod.lift ((openLocalizationUnit j).app M) ((openLocalizationUnit k).app M)
/-- The signed original restriction difference to the actual overlap. -/
def sheafDifference :
    (openLocalization j).obj M ⨯ (openLocalization k).obj M ⟶
      (openLocalization (a ≫ j)).obj M :=
  prod.fst ≫ openLocalizationMap a j M - prod.snd ≫ sheafSecondRestriction a b j k h M
/-- The original restriction units are annihilated by the signed difference. -/
theorem sheafAugmentation_difference :
    sheafAugmentation j k M ≫ sheafDifference a b j k h M = 0 := by
  simp only [sheafAugmentation, sheafDifference, Preadditive.comp_sub,
    ← Category.assoc, prod.lift_fst, prod.lift_snd, sheafSecondRestriction]
  rw [Category.assoc, openLocalizationUnit_map, ← Category.assoc,
    openLocalizationUnit_map, openLocalizationUnit_congr, sub_self]
/-- The original two-open restriction sequence of module sheaves. -/
def sheafSequence : ShortComplex X.Modules :=
  ShortComplex.mk (sheafAugmentation j k M) (sheafDifference a b j k h M)
    (sheafAugmentation_difference a b j k h M)
end AlgebraicGeometry.Scheme.Modules.TwoOpen
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : IsPullback a b j k) (M : X.Modules)
/-- The original augmented restrictions agree on the common actual overlap. -/
theorem sheaf_restriction_compatibility :
    (openLocalizationUnit j).app M ≫ openLocalizationMap a j M =
      (openLocalizationUnit k).app M ≫ sheafSecondRestriction a b j k h.w M := by
  rw [openLocalizationUnit_map, sheafSecondRestriction, ← Category.assoc,
    openLocalizationUnit_map, openLocalizationUnit_congr]
/-- On the first chart the original signed Čech sheaf sequence is split exact. -/
theorem sheafSequence_restrict_left_shortExact :
    ((sheafSequence a b j k h.w M).map (Scheme.Modules.restrictFunctor j)).ShortExact := by
  let F := Scheme.Modules.restrictFunctor j
  let α := (openLocalizationUnit j).app M
  let β := (openLocalizationUnit k).app M
  let γ := openLocalizationMap a j M
  let δ := sheafSecondRestriction a b j k h.w M
  have hc : α ≫ γ = β ≫ δ := sheaf_restriction_compatibility a b j k h M
  let : IsIso (F.map α) := isIso_restrict_openLocalizationUnit j M
  let : IsIso (F.map (openLocalizationMap b k M)) :=
    isIso_restrict_openLocalizationMap b a k j h.flip M
  let : IsIso (F.map δ) := by
    dsimp only [δ, sheafSecondRestriction]
    rw [Functor.map_comp]
    infer_instance
  change ((productSequence α β γ δ hc).map F).ShortExact
  exact productSequence_map_shortExact F α β γ δ hc
/-- On the second chart the other two original components give split exactness. -/
theorem sheafSequence_restrict_right_shortExact :
    ((sheafSequence a b j k h.w M).map (Scheme.Modules.restrictFunctor k)).ShortExact := by
  let F := Scheme.Modules.restrictFunctor k
  let α := (openLocalizationUnit j).app M
  let β := (openLocalizationUnit k).app M
  let γ := openLocalizationMap a j M
  let δ := sheafSecondRestriction a b j k h.w M
  have hc : α ≫ γ = β ≫ δ := sheaf_restriction_compatibility a b j k h M
  let : IsIso (F.map β) := isIso_restrict_openLocalizationUnit k M
  let : IsIso (F.map γ) := isIso_restrict_openLocalizationMap a b j k h M
  change ((productSequence α β γ δ hc).map F).ShortExact
  exact ShortComplex.shortExact_of_iso (productSequenceMapIso F α β γ δ hc).symm
    (productSequence_shortExact_right _ _ _ _ _)
/-- The original two-open Čech sequence is short exact for every module sheaf. -/
theorem sheafSequence_shortExact
    (hcover : ∀ x : X, (∃ y : U, j y = x) ∨ (∃ z : V, k z = x)) :
    (sheafSequence a b j k h.w M).ShortExact := by
  let T : Bool → Scheme.{u} := fun i => if i then U else V
  let c : ∀ i, T i ⟶ X := fun i => by
    cases i
    · exact k
    · exact j
  let : ∀ i, IsOpenImmersion (c i) := fun i => by
    cases i <;> dsimp [c] <;> infer_instance
  apply shortExact_of_restrict_openCover T c
    (fun x => by
      rcases hcover x with ⟨y, hy⟩ | ⟨z, hz⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, z, hz⟩)
  intro i
  cases i
  · exact sheafSequence_restrict_right_shortExact a b j k h M
  · exact sheafSequence_restrict_left_shortExact a b j k h M
end AlgebraicGeometry.Scheme.Modules.TwoOpen
end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.TwoOpen
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
/-- The transported second restriction is natural in the original sheaf morphism. -/
theorem sheafSecondRestriction_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (openLocalization k).map φ ≫ sheafSecondRestriction a b j k h N =
      sheafSecondRestriction a b j k h M ≫ (openLocalization (a ≫ j)).map φ := by
  dsimp only [sheafSecondRestriction]
  rw [← Category.assoc, openLocalizationMap_naturality, Category.assoc,
    (openLocalizationCongr h.symm).hom.naturality, ← Category.assoc]
/-- The original restrictions give a morphism of the actual Čech sheaf sequences. -/
def sheafSequenceMap {M N : X.Modules} (φ : M ⟶ N) :
    sheafSequence a b j k h M ⟶ sheafSequence a b j k h N where
  τ₁ := φ
  τ₂ := prod.map ((openLocalization j).map φ) ((openLocalization k).map φ)
  τ₃ := (openLocalization (a ≫ j)).map φ
  comm₁₂ := by
    apply prod.hom_ext
    · simpa [sheafSequence, sheafAugmentation] using (openLocalizationUnit j).naturality φ
    · simpa [sheafSequence, sheafAugmentation] using (openLocalizationUnit k).naturality φ
  comm₂₃ := by
    dsimp only [sheafSequence, sheafDifference]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      prod.map_fst_assoc, prod.map_snd_assoc]
    rw [openLocalizationMap_naturality, sheafSecondRestriction_naturality]
/-- The original sheaf Čech sequence is functorial, with literal identity and composition maps. -/
def sheafSequenceFunctor : X.Modules ⥤ ShortComplex X.Modules where
  obj M := sheafSequence a b j k h M
  map φ := sheafSequenceMap a b j k h φ
  map_id M := by
    ext : 1 <;> simp [sheafSequenceMap, sheafSequence]
  map_comp φ ψ := by
    ext : 1 <;> simp [sheafSequenceMap, sheafSequence, Functor.map_comp]
end AlgebraicGeometry.Scheme.Modules.TwoOpen
end
