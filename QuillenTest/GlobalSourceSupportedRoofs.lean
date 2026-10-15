/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedEquality

/-!
# Global roofs with prescribed source support

Regression statements retain source vanishing on a specified compact open while
representing local arrows and isomorphisms or producing global chain homotopies.
The special cases include an empty restriction open and a source that is
derived-zero on the whole scheme.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.GlobalSourceSupportedRoofs
open Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- The same actual supported source represents the original isomorphism in
both directions, with two genuinely weak restricted legs. -/
theorem original_supported_isomorphism_roof {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (e : (toDerived U).obj ((restrict j).obj A) ≅ (toDerived U).obj ((restrict j).obj B)) :
    ∃ (M : Complex X) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ QuasiIso ((restrict j).map g) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      (toDerived U).map ((restrict j).map g) ≫ e.inv = (toDerived U).map ((restrict j).map q) := by
  obtain ⟨M,q,g,hM,hq,hg,hzM⟩ := exists_source_supported_derived_roof j T hT hA hB hzA e.hom
  have hi : IsIso ((toDerived U).map ((restrict j).map g)) := by rw [← hg]; infer_instance
  refine ⟨M,q,g,hM,hq,(DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp hi,hzM,?_⟩
  rw [← hg,Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- Source support is enough for a roof recovering any prescribed original
local arrow; no support condition is imposed on the target. -/
theorem original_arrow_recovery {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (φ : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj B)) :
    ∃ (M : Complex X) (q : M ⟶ A) (g : M ⟶ B) (_ : QuasiIso ((restrict j).map q)),
      locallyPerfect X M ∧ IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      inv ((toDerived U).map ((restrict j).map q)) ≫ (toDerived U).map ((restrict j).map g) = φ :=
        by
  obtain ⟨M,q,g,hM,hq,hg,hzM⟩ := exists_source_supported_derived_roof j T hT hA hB hzA φ
  refine ⟨M,q,g,hq,hM,hzM,?_⟩
  rw [← hg,IsIso.inv_hom_id_assoc]

/-- A genuine global homotopy denominator keeps the original prescribed support. -/
theorem original_supported_chain_homotopy {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (f g : A ⟶ B)
    (heq : (toDerived U).map ((restrict j).map f) = (toDerived U).map ((restrict j).map g)) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      Nonempty (Homotopy (q ≫ f) (q ≫ g)) :=
  exists_source_supported_homotopy_of_restrict_derived_eq j T hT hA b hB hzA f g heq

/-- Empty original restriction imposes no hidden nonempty-cover premise. -/
theorem empty_open_supported_roof {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (T : X.Opens) (hT : IsCompact (T : Set X)) {A B : Complex X}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (φ : (toDerived (⊥ : X.Opens).toScheme).obj ((restrict (⊥ : X.Opens).ι).obj A) ⟶
      (toDerived (⊥ : X.Opens).toScheme).obj ((restrict (⊥ : X.Opens).ι).obj B)) :
    ∃ (M : Complex X) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict (⊥ : X.Opens).ι).map q) ∧
      (toDerived (⊥ : X.Opens).toScheme).map ((restrict (⊥ : X.Opens).ι).map q) ≫ φ =
        (toDerived (⊥ : X.Opens).toScheme).map ((restrict (⊥ : X.Opens).ι).map g) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) := by
  let : CompactSpace (⊥ : X.Opens).toScheme := isCompact_iff_compactSpace.mp isCompact_empty
  exact exists_source_supported_derived_roof _ T hT hA hB hzA φ

/-- Source vanishing on the whole scheme forces the produced source to be
actually derived-zero globally, while retaining the original roof equation. -/
theorem globally_zero_source_roof {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : Complex X}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B) (hzA : IsZero ((toDerived X).obj A))
    (φ : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj B)) :
    ∃ (M : Complex X) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ IsZero ((toDerived X).obj M) ∧
      (toDerived U).map ((restrict j).map q) ≫ φ = (toDerived U).map ((restrict j).map g) := by
  have hzT := isZero_toDerived_restrict_of_isZero (⊤ : X.Opens).ι hzA
  obtain ⟨M,q,g,hM,hq,hg,hzM⟩ := exists_source_supported_derived_roof j ⊤ isCompact_univ hA hB hzT φ
  let : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact ⟨M,q,g,hM,hq,(isZero_toDerived_restrict_iff_of_isIso (⊤ : X.Opens).ι M).mp hzM,hg⟩

end QuillenTest.GlobalSourceSupportedRoofs
