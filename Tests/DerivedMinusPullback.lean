/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedMinusPullbackComposition

/-! Semantic consumers of genuine ambient bounded-above derived pullback. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w₁ w₂ w₃
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf
namespace Quillen.Tests.DerivedMinusPullback

/-- Actual ambient morphisms lift uniquely to the localization of bounded complexes,
with no projective or injective existence assumption on the abelian category. -/
theorem ambient_bounded_morphism_lift (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K L : (boundedAboveQuasiIso C).Localization)
    (a : (boundedAboveLocalizationToMinus C).obj K ⟶
      (boundedAboveLocalizationToMinus C).obj L) :
    ∃! b : K ⟶ L, (boundedAboveLocalizationToMinus C).map b = a := by
  let F := boundedAboveLocalizationToMinusFullyFaithful C
  exact ⟨F.preimage a, F.map_preimage a, fun b hb => F.map_injective (hb.trans (F.map_preimage
    a).symm)⟩

/-- Comparisons of actual projective models commute with the original augmentations
up to an actual chain homotopy, before any derived localization. -/
theorem actual_projective_comparison (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughProjectives C] {K L : BoundedAboveComplex C} (s : K ⟶ L) :
    Nonempty (Homotopy (projectiveModelMap s ≫ projectiveModelπ L)
      (projectiveModelπ K ≫ s.hom)) :=
  ⟨projectiveModelMapHomotopy s⟩

/-- The original sheaf augmentation induces genuine isomorphisms on all homology objects. -/
theorem actual_flat_model_homology (X : Scheme.{u}) (K : BoundedAboveComplex X.Modules) (n : ℤ) :
    IsIso ((homologyFunctor X.Modules (.up ℤ) n).map (flatModelπ X K)) := by
  change IsIso (homologyMap (flatModelπ X K) n)
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance

/-- Arbitrary scheme pullback of the constructed comparison inverts an original sheaf
quasi-isomorphism, without assuming its underlying presheaf map is a quasi-isomorphism. -/
theorem original_sheaf_quasiIso_inverted {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] {K L : BoundedAboveComplex Y.Modules}
    (s : K ⟶ L) [QuasiIso s.hom] :
    IsIso (DerivedCategory.Q.map
      ((Quillen.PerfectComplexes.pullbackComplex f).map (flatModelMap s))) := by
  have := pullback_flatModelMap_quasiIso f s
  infer_instance

/-- The actual derived map formula commutes with the original bounded-complex localization. -/
theorem derived_map_formula {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} Y.Modules] [HasDerivedCategory.{w₂} X.Modules]
    {K L : BoundedAboveComplex Y.Modules} (s : K ⟶ L) :
    (derivedPullbackMinus f).map ((boundedAboveQMinus Y.Modules).map s) ≫
      (derivedPullbackMinusFactors f).hom.app L =
    (derivedPullbackMinusFactors f).hom.app K ≫
      (boundedAboveQMinus X.Modules).map (pullbackFlatModelBoundedMap f s) := by
  exact (derivedPullbackMinusFactors f).hom.naturality s

/-- The computed derived pullback of every bounded representative is its actual geometric flat
  model. -/
def actual_derived_object {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} Y.Modules] [HasDerivedCategory.{w₂} X.Modules]
    (K : BoundedAboveComplex Y.Modules) :
    ((derivedPullbackMinus f).obj ((boundedAboveQMinus Y.Modules).obj K)).obj ≅
      DerivedCategory.Q.obj ((Quillen.PerfectComplexes.pullbackComplex f).obj (flatModel Y K)) :=
  derivedPullbackMinusObjectIso f K

/-- Identity pullback acts naturally as the identity on every ambient derived morphism. -/
theorem derived_identity_natural (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]
    {K L : DerivedCategory.Minus X.Modules} (a : K ⟶ L) :
    (derivedPullbackMinus (𝟙 X)).map a ≫ (derivedPullbackMinusIdIso X).hom.app L =
      (derivedPullbackMinusIdIso X).hom.app K ≫ a :=
  (derivedPullbackMinusIdIso X).hom.naturality a

/-- Two successive arbitrary derived pullbacks of a genuinely flat input agree with
the original termwise pullback along the composite. -/
def successive_pullbacks_on_flat_input {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w₁} Z.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasDerivedCategory.{w₃} X.Modules] (K : BoundedAboveComplex Z.Modules)
    (hK : ∀ n, stalkwiseFlat Z (K.obj.X n)) :
    ((derivedPullbackMinus f).obj
      ((derivedPullbackMinus g).obj ((boundedAboveQMinus Z.Modules).obj K))).obj ≅
      DerivedCategory.Q.obj ((Quillen.PerfectComplexes.pullbackComplex (f ≫ g)).obj K.obj) :=
  (DerivedCategory.Minus.ι).mapIso
      ((derivedPullbackMinusCompIso f g).app ((boundedAboveQMinus Z.Modules).obj K)).symm ≪≫
    derivedPullbackMinusFlatObjectIso (f ≫ g) K hK

/-- The genuine resolved functor sends sums of original chain maps to sums of derived maps. -/
theorem resolved_pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] {K L : BoundedAboveComplex Y.Modules} (s t : K ⟶ L) :
    (resolvedPullbackFunctor f).map (s + t) =
      (resolvedPullbackFunctor f).map s + (resolvedPullbackFunctor f).map t :=
  (resolvedPullbackFunctor f).map_add

end Quillen.Tests.DerivedMinusPullback
