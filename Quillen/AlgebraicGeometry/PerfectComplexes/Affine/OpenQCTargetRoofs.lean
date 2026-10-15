/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedStabilizedExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.InjectiveCounit
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Models
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionRoofs

/-! # Source-supported roofs to original lower-bounded QC all-sheaf targets

Genuine affine module reconstruction and globally weak common fractions keep
both final chain numerators at the unchanged original sheaf complexes. The
module support theorem is applied only to the genuine associated module
models. Its support conclusion then passes through the actual global weak
comparison, rather than through an unproved underived pushforward property.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- An original derived morphism from a globally perfect source to an original
lower-bounded QC target has actual locally weak global perfect denominators.
Every original compact-open vanishing condition on the source is retained. -/
lemma exists_open_roof_to_lowerBounded_quasicoherent_target
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hBqc : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj A) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj B)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (g : M ⟶ B),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict W.ι).map q) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map q) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map g) ∧
      ∀ (Z : (Spec R).Opens), IsCompact (Z : Set (Spec R)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj A)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj M)) := by
  obtain ⟨A₀, hA₀, ⟨eA⟩⟩ := locallyPerfect_exists_moduleStrictPerfect_representative R hA
  obtain ⟨B₀, hB₀, ⟨eB⟩⟩ := exists_lowerBounded_module_representative B b hBqc
  let β := (restrictDerivedIso W.ι eA).hom ≫ α ≫ (restrictDerivedIso W.ι eB).inv
  obtain ⟨P, hP, t, a, ht, ha, hsupport⟩ :=
    exists_quasiCompact_open_module_roof_preserving_source_support R W hW hA₀ b β
  obtain ⟨M, s, q, g, hs, hq, hg⟩ := OpenDerivedImage.common_global_right_fraction
    ((toDerived (Spec R)).map ((associatedComplex R).map t) ≫ eA.hom)
    ((toDerived (Spec R)).map ((associatedComplex R).map a) ≫ eB.hom)
  have hM : locallyPerfect (Spec R) M :=
    (locallyPerfect_iff_of_quasiIso s).mpr (locallyPerfect_of_strictPerfect
      (strictPerfect_associated R hP))
  have hqr := congrArg (restrictDerivedHom W.ι) hq
  have hgr := congrArg (restrictDerivedHom W.ι) hg
  simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hqr hgr
  have hweak : QuasiIso ((restrict W.ι).map q) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso W.toScheme.Modules _).mp
    change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map q))
    rw [← hqr]
    change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map s) ≫
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫
        (restrictDerivedIso W.ι eA).hom)
    infer_instance
  refine ⟨M, q, g, hM, hweak, ?_, ?_⟩
  · rw [← hqr, ← hgr]
    simp only [Category.assoc]
    change (toDerived W.toScheme).map ((restrict W.ι).map s) ≫
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫
        (restrictDerivedIso W.ι eA).hom ≫ α =
      (toDerived W.toScheme).map ((restrict W.ι).map s) ≫
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map a)) ≫
          (restrictDerivedIso W.ι eB).hom
    rw [← ha]
    simp only [β, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro Z hZ hz
    have hA₀Z : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj
      A₀))) :=
      hz.of_iso (restrictDerivedIso Z.ι eA)
    obtain ⟨sZ, hsZ⟩ := exists_finite_principal_cover R Z hZ
    have hpZ : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj
      P))) := by
      apply isZero_restrict_associated_of_principalUnion R Z sZ hsZ
      intro r hr
      apply hsupport r
      apply isZero_localize_of_isZero_restrict_associated R Z A₀ hA₀Z r
      rw [← hsZ]
      exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hr
    exact hpZ.of_iso (asIso ((toDerived Z.toScheme).map ((restrict Z.ι).map s)))

lemma exists_immersion_roof_to_lowerBounded_quasicoherent_target
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R)
    [IsOpenImmersion j] [CompactSpace U]
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hBqc : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj B)) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A) (g : M ⟶ B),
      locallyPerfect (Spec R) M ∧ QuasiIso ((restrict j).map q) ∧
      (toDerived U).map ((restrict j).map q) ≫ α = (toDerived U).map ((restrict j).map g) ∧
      ∀ (Z : (Spec R).Opens), IsCompact (Z : Set (Spec R)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj A)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj M)) := by
  let W := j.opensRange
  let e := j.isoOpensRange.symm
  let c : restrict j ⋙ restrict e.hom ≅ restrict W.ι :=
    restrictCompIso e.hom j ≪≫ eqToIso (restrict_congr j.isoOpensRange_inv_comp)
  let Q := toDerived W.toScheme
  let α' := Q.map (c.inv.app A) ≫ restrictDerivedHom e.hom α ≫ Q.map (c.hom.app B)
  obtain ⟨M, q, g, hM, hq, hg, hs⟩ :=
    exists_open_roof_to_lowerBounded_quasicoherent_target R W (isCompact_range j.continuous)
      hA b hBqc α'
  have hq' : QuasiIso ((restrict e.hom).map ((restrict j).map q)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app M) (c.app A) (c.hom.naturality q).symm)).mpr hq
  refine ⟨M, q, g, hM, (quasiIso_restrict_iff_of_isIso e.hom _).mp hq', ?_, hs⟩
  apply restrictDerivedHom_injective_of_isIso e.hom
  simp only [restrictDerivedHom_comp, restrictDerivedHom_map]
  apply (cancel_mono (Q.map (c.hom.app B))).mp
  rw [Category.assoc]
  change Q.map ((restrict j ⋙ restrict e.hom).map q) ≫
    restrictDerivedHom e.hom α ≫ Q.map (c.hom.app B) =
      Q.map ((restrict j ⋙ restrict e.hom).map g) ≫ Q.map (c.hom.app B)
  have hqnat := congrArg Q.map (c.hom.naturality q)
  have hgnat := congrArg Q.map (c.hom.naturality g)
  simp only [Functor.map_comp] at hqnat hgnat
  have hα : restrictDerivedHom e.hom α ≫ Q.map (c.hom.app B) = Q.map (c.hom.app A) ≫ α' := by
    dsimp only [α']
    rw [← Category.assoc, ← Q.map_comp, c.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hα, ← Category.assoc, hqnat, Category.assoc, hg, hgnat]

end Quillen.PerfectComplexes.Affine
