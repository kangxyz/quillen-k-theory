/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.GlobalRoofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Global perfect roof regression statements

Records roofs on compact opens of qcqs schemes, denominators for lower-bounded
targets with quasicoherent homology, and denominator comparisons for local
equalities. Further statements retain chain homotopies, the empty-open case,
and factorization through the supported cone of a denominator.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.GlobalPerfectRoofs
open Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- An arbitrary original derived isomorphism on the compact open has two
actual global perfect roof legs weak on that same open. -/
theorem original_isomorphism_roof {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (e : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ≅
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ QuasiIso ((restrict j).map g) ∧
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g) ≫ e.inv =
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) := by
  obtain ⟨M, q, g, hM, hq, hg⟩ := qcqs_hasDerivedRoofs j A B hA hB e.hom
  have hi : IsIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g))
    := by rw [← hg]; infer_instance
  refine ⟨M, q, g, hM, hq, (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp hi, ?_⟩
  rw [← hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual global denominator annihilates the original arbitrary derived
map into the original lower-bounded QC supported target. -/
theorem original_supported_denominator {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      (DerivedCategory.Q (C := X.Modules)).map q ≫ α = 0 :=
  qcqs_hasSupportedQCDenominators_of_openImmersion j A B hA b inferInstance hB hzB α

/-- An original local equality is cleared globally by one actual denominator,
without a supplied global roof or supported-factorization hypothesis. -/
theorem original_derived_equality {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α β : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
    (h : restrictDerivedHom j α = restrictDerivedHom j β) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      (DerivedCategory.Q (C := X.Modules)).map q ≫ α = (DerivedCategory.Q (C := X.Modules)).map q
        ≫ β :=
  exists_denominator_of_restrictDerivedHom_eq j
    (qcqs_hasSupportedQCDenominators_of_openImmersion j) hA b hB α β h

/-- Equality of original chain maps after derived restriction gives an actual
global chain homotopy after a perfect source denominator weak on the same open. -/
theorem original_chain_equality_homotopy {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent) (f g : A ⟶ B)
    (h : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map f) =
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      Nonempty (Homotopy (q ≫ f) (q ≫ g)) := by
  obtain ⟨P, q, hP, hq, hfg⟩ := original_derived_equality j hA b hB
    ((DerivedCategory.Q (C := X.Modules)).map f) ((DerivedCategory.Q (C := X.Modules)).map g)
      (by simpa only [restrictDerivedHom_map] using h)
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  have he : DerivedCategory.Q.{u+1}.map (q ≫ f) = DerivedCategory.Q.{u+1}.map (q ≫ g) := by
    change (DerivedCategory.Q (C := X.Modules)).map (q ≫ f) =
      (DerivedCategory.Q (C := X.Modules)).map (q ≫ g)
    simpa only [Functor.map_comp] using hfg
  obtain ⟨M, s, hs, ⟨H⟩⟩ :=
    Quillen.CochainComplex.exists_pre_quasiIso_homotopy_of_derived_eq (q ≫ f) (q ≫ g) he
  refine ⟨M, s ≫ q, (locallyPerfect_iff_of_quasiIso s).mpr hP, ?_, ?_⟩
  · rw [(restrict j).map_comp]
    infer_instance
  · exact ⟨by simpa only [Category.assoc] using H⟩

/-- The global result includes the actual empty open and arbitrary original
local morphism, without choosing an inhabitant or an affine presentation. -/
theorem empty_open_original_roof {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (hB : locallyPerfect X B)
    (α : (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
      ((restrict (⊥ : X.Opens).ι).obj A) ⟶
      (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj B)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
      QuasiIso ((restrict (⊥ : X.Opens).ι).map q) ∧
      (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).map
        ((restrict (⊥ : X.Opens).ι).map q) ≫ α =
        (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).map
          ((restrict (⊥ : X.Opens).ι).map g) := by
  let : CompactSpace (⊥ : X.Opens).toScheme := isCompact_iff_compactSpace.mp (by simp)
  exact qcqs_hasDerivedRoofs (⊥ : X.Opens).ι A B hA hB α

/-- The genuine global denominator has an actual supported cone and the
original cone inclusion factors the original derived morphism. -/
theorem original_supported_cone_factorization {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] {A B : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A)
      (γ : (DerivedCategory.Q (C := X.Modules)).obj (CochainComplex.mappingCone q) ⟶
        (DerivedCategory.Q (C := X.Modules)).obj B),
      locallyPerfect X (CochainComplex.mappingCone q) ∧
      IsZero ((DerivedCategory.Q (C := U.Modules)).obj
        ((restrict j).obj (CochainComplex.mappingCone q))) ∧
      (DerivedCategory.Q (C := X.Modules)).map (CochainComplex.mappingCone.inr q) ≫ γ = α := by
  obtain ⟨M, q, hM, hq, hqα⟩ := original_supported_denominator j hA b hB hzB α
  obtain ⟨γ, hγ⟩ := CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂ _
    (DerivedCategory.mappingCone_triangle_distinguished q) α hqα
  refine ⟨M, q, γ, locallyPerfect_mappingCone hM hA q, ?_, hγ.symm⟩
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished ((restrict j).map q)) (by
      change IsIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q))
      infer_instance)).of_iso
      ((DerivedCategory.Q (C := U.Modules)).mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso q
        (Scheme.Modules.restrictFunctor j)))

end QuillenTest.GlobalPerfectRoofs
