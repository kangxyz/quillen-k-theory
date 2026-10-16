/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.GlobalRoofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Original global denominators retain a prescribed compact-open source support -/
@[expose] public section

open HomologicalComplex


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves

/-- The actual MV obstruction vanishes because the target is zero on the first
piece. Source vanishing on the second piece then kills the original map on
the union. No general local-nullity reflection is used. -/
lemma derivedHom_eq_zero_on_union_of_source_target_support {X : Scheme.{u}}
    (U T : X.Opens) {A B : CochainComplex X.Modules ℤ}
    (hB : IsZero ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj B)))
    (hA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    restrictDerivedHom (U ⊔ T).ι α = 0 := by
  let j := X.homOfLE (le_sup_left : U ≤ U ⊔ T)
  let k := X.homOfLE (le_sup_right : T ≤ U ⊔ T)
  let cU : restrict (U ⊔ T).ι ⋙ restrict j ≅ restrict U.ι :=
    restrictCompIso j (U ⊔ T).ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_left))
  let cT : restrict (U ⊔ T).ι ⋙ restrict k ≅ restrict T.ι :=
    restrictCompIso k (U ⊔ T).ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_right))
  have hBU : IsZero ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
    ((restrict j).obj ((restrict (U ⊔ T).ι).obj B))) :=
    hB.of_iso ((DerivedCategory.Q (C := U.toScheme.Modules)).mapIso (cU.app B))
  have hAT : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj
    ((restrict k).obj ((restrict (U ⊔ T).ι).obj A))) :=
    hA.of_iso ((DerivedCategory.Q (C := T.toScheme.Modules)).mapIso (cT.app A))
  apply derivedHom_eq_zero_of_target_zero_and_cover j k _ hBU
  · exact hAT.eq_of_src _ _
  · intro x
    rcases x.property with hx | hx
    · exact Or.inl ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    · exact Or.inr ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩

namespace OpenDerivedImage

/-- A genuine global denominator for a supported QC target preserves the
original source vanishing on any additional prescribed compact open. -/
lemma exists_source_supported_denominator_on_opens {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U T : X.Opens)
    (hU : IsCompact (U : Set X)) (hT : IsCompact (T : Set X))
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj B)))
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict U.ι).map q) ∧
      IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj M)) ∧
        (DerivedCategory.Q (C := X.Modules)).map q ≫ α = 0 := by
  let Y := U ⊔ T
  let : CompactSpace Y.toScheme := isCompact_iff_compactSpace.mp (hU.union hT)
  obtain ⟨M, q, hM, hq, hqα⟩ := exists_denominator_of_restrictDerivedHom_zero Y.ι
    (qcqs_hasSupportedQCDenominators Y (hU.union hT)) hA b hB α
    (derivedHom_eq_zero_on_union_of_source_target_support U T hzB hzA α)
  let cU : restrict Y.ι ⋙ restrict (X.homOfLE (le_sup_left : U ≤ Y)) ≅ restrict U.ι :=
    restrictCompIso _ Y.ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_left))
  let cT : restrict Y.ι ⋙ restrict (X.homOfLE (le_sup_right : T ≤ Y)) ≅ restrict T.ι :=
    restrictCompIso _ Y.ι ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X le_sup_right))
  have hqU : QuasiIso ((restrict U.ι).map q) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (cU.app M) (cU.app A) (cU.hom.naturality q).symm)).mp
        (inferInstanceAs (QuasiIso ((restrict (X.homOfLE (le_sup_left : U ≤ Y))).map ((restrict
          Y.ι).map q))))
  have hqT : QuasiIso ((restrict T.ι).map q) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (cT.app M) (cT.app A) (cT.hom.naturality q).symm)).mp
        (inferInstanceAs (QuasiIso ((restrict (X.homOfLE (le_sup_right : T ≤ Y))).map ((restrict
          Y.ι).map q))))
  exact ⟨M, q, hM, hqU, hzA.of_iso (asIso ((DerivedCategory.Q (C := T.toScheme.Modules)).map
    ((restrict T.ι).map q))), hqα⟩

/-- The same source-support conclusion for any original compact open immersion. -/
lemma exists_source_supported_denominator {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj M)) ∧
        (DerivedCategory.Q (C := X.Modules)).map q ≫ α = 0 := by
  obtain ⟨M, q, hM, hq, hzM, hqα⟩ := exists_source_supported_denominator_on_opens j.opensRange T
    (isCompact_range j.continuous) hT hA b hB (isZero_restrict_opensRange_of_isZero j hzB) hzA α
  let c : restrict j.opensRange.ι ⋙ restrict j.isoOpensRange.hom ≅ restrict j :=
    restrictCompIso _ _ ≪≫ eqToIso (restrict_congr j.isoOpensRange_hom_ι)
  have hqj : QuasiIso ((restrict j).map q) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app M) (c.app A) (c.hom.naturality q).symm)).mp
        (inferInstanceAs (QuasiIso ((restrict j.isoOpensRange.hom).map ((restrict
          j.opensRange.ι).map q))))
  exact ⟨M, q, hM, hqj, hzM, hqα⟩

end OpenDerivedImage
end Quillen.PerfectComplexes
