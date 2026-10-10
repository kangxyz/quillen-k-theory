/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.BoundedFlatReplacement
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ReducedFlatCover
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.BoundedFlatPullback

/-! Semantic consumers of genuine bounded-above flat replacements. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.SchemeSheaf
namespace Quillen.Tests.BoundedFlatReplacements

/-- A bounded-above complex of arbitrary sheaves has a replacement with exactly its original bound.
  -/
theorem actual_complex_replacement (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) :
    ∃ (P : CochainComplex X.Modules ℤ) (p : P ⟶ K), QuasiIso p ∧
      (∀ n, stalkwiseFlat X (P.X n)) ∧ (∀ n, b < n → IsZero (P.X n)) := by
  have : K.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff K b).mpr hb
  obtain ⟨P, p, hp, hP, hPb⟩ := exists_boundedAbove_flat_complex_replacement X K b
  exact ⟨P, p, hp, hP, (fun n hn => P.isZero_of_isStrictlyLE b n hn)⟩

/-- The actual counit appearing in the replacement agrees in each degree with sheafification. -/
theorem actual_counit_component (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (sheafificationComplexCounitIso X K).hom.f n =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (K.X n) := by
  simp

/-- Free Yoneda projectives solve actual lifting problems of module presheaves. -/
theorem actual_freeYoneda_lift (X : Scheme.{u}) (U : X.Opens)
    {P Q : PresheafOfModules.{u} X.ringCatSheaf.obj} (q : P ⟶ Q) [Epi q]
    (s : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U) ⟶ Q) :
    ∃ t, t ≫ q = s := by
  exact ⟨Projective.factorThru s q, Projective.factorThru_comp s q⟩

/-- Applying exact sheafification to an arbitrary actual projective gives flat stalks. -/
theorem actual_projective_sheafification_flat (X : Scheme.{u})
    (P : PresheafOfModules.{u} X.ringCatSheaf.obj) [Projective P] :
    stalkwiseFlat X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) :=
  stalkwiseFlat_sheafify_projective X P

/-- The reduction really kills zero maps, making it safe for complex differentials. -/
theorem reduced_cover_kills_zero (X : Scheme.{u}) (M N : X.Modules) :
    (reducedFlatCoverFunctor X).map (0 : M ⟶ N) = 0 := by simp

/-- The reduced flat complex cover has an actual degreewise epic augmentation. -/
theorem reduced_cover_degree_epi (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    Epi (((reducedFlatCoverComplexAugmentation X).app K).f n) := inferInstance

/-- For a genuinely flat original complex, a new replacement augmentation remains a
quasi-isomorphism after any scheme morphism, with the same upper bound. -/
theorem replacement_augmentation_survives_arbitrary_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex Y.Modules ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ n, stalkwiseFlat Y (K.X n)) :
    ∃ (P : CochainComplex Y.Modules ℤ) (p : P ⟶ K), QuasiIso p ∧
      (∀ n, stalkwiseFlat Y (P.X n)) ∧ P.IsStrictlyLE b ∧
      QuasiIso ((Quillen.PerfectComplexes.pullbackComplex f).map p) := by
  obtain ⟨P, p, hp, hP, hb⟩ := exists_boundedAbove_flat_complex_replacement Y K b
  let : QuasiIso p := hp
  exact ⟨P, p, hp, hP, hb, quasiIso_pullback_of_boundedAbove_stalkwiseFlat f hP hK b b
    (fun n hn => P.isZero_of_isStrictlyLE b n hn)
    (fun n hn => K.isZero_of_isStrictlyLE b n hn) p⟩

end Quillen.Tests.BoundedFlatReplacements
