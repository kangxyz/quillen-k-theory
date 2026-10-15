/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.SupportedAffineExtension
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalDensity

/-!
# Global qcqs perfect complements with prescribed support

For a quasi-compact quasi-separated scheme X and compact opens U and Z, an
original perfect complex E on U vanishing on U intersect Z is an actual
derived retract of the restriction of a global perfect complex P vanishing
on Z. An actual perfect complement C gives the original derived isomorphism
P restricted to U isomorphic to E plus C. The final wrapper retains any
original compact open immersion, rather than only its image presentation.

Finite affine-cover induction uses genuine supported stabilization and local
weak gluing maps at every step. The finite-family theorem needs only
quasi-separatedness of X; compactness is required to exhaust X by finitely
many affine charts. No global affine-diagonal or fixed stabilization
multiplicity is assumed. Global morphism roofs are a separate theorem.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

lemma exists_supported_perfect_retract_on_finite_affine_union {X : Scheme.{u}} [QuasiSeparatedSpace
  X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (hz : IsZero ((toDerived (U.ι ⁻¹ᵁ Z).toScheme).obj ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E)))
    (s : Finset X.affineOpens) :
    ∃ (hUS : U ≤ U ⊔ s.sup (fun V => V.val))
      (P : Complex (U ⊔ s.sup (fun V => V.val)).toScheme),
      locallyPerfect (U ⊔ s.sup (fun V => V.val)).toScheme P ∧
      Nonempty (Retract ((toDerived U.toScheme).obj E)
        ((toDerived U.toScheme).obj ((restrict (X.homOfLE hUS)).obj P))) ∧
      IsZero ((toDerived ((U ⊔ s.sup (fun V => V.val)).ι ⁻¹ᵁ Z).toScheme).obj
        ((restrict ((U ⊔ s.sup (fun V => V.val)).ι ⁻¹ᵁ Z).ι).obj P)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq]
    refine ⟨le_rfl, E, hE, ⟨Retract.ofIso ((toDerived U.toScheme).mapIso ?_)⟩, hz⟩
    exact ((eqToIso (restrict_congr (X.homOfLE_rfl U)) ≪≫ restrictIdIso U.toScheme).app E).symm
  | @insert V s hV ih =>
    rw [Finset.sup_insert, show U ⊔ (V.val ⊔ s.sup (fun V => V.val)) =
      (U ⊔ s.sup (fun V => V.val)) ⊔ V.val by ac_rfl]
    let S := U ⊔ s.sup (fun V => V.val)
    have hS : IsCompact (S : Set X) := hU.union (isCompact_finite_affine_sup s)
    let : CompactSpace S.toScheme := isCompact_iff_compactSpace.mp hS
    let : IsAffine V.val.toScheme := V.property
    let : QuasiSeparatedSpace (S ⊔ V.val).toScheme :=
      QuasiSeparatedSpace.of_isOpenEmbedding (S ⊔ V.val).ι.isOpenEmbedding
    obtain ⟨hUS, P, hP, ⟨r⟩, hPZ⟩ := ih
    let i := X.homOfLE hUS
    let j := X.homOfLE (le_sup_left : S ≤ S ⊔ V.val)
    let k := X.homOfLE (le_sup_right : V.val ≤ S ⊔ V.val)
    have hcover (x : (S ⊔ V.val).toScheme) : x ∈ Set.range j ∨ x ∈ Set.range k := by
      rcases x.property with hx | hx
      · exact Or.inl ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
      · exact Or.inr ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    let T := S ⊔ V.val
    let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp (hS.union V.property.isCompact)
    have hTZ := T.ι.isCompact_preimage hZ
    have hPZ' : IsZero ((toDerived (j ⁻¹ᵁ (T.ι ⁻¹ᵁ Z)).toScheme).obj
        ((restrict (j ⁻¹ᵁ (T.ι ⁻¹ᵁ Z)).ι).obj P)) := by
      have he : j ⁻¹ᵁ (T.ι ⁻¹ᵁ Z) = S.ι ⁻¹ᵁ Z := by
        rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
      rw [he]
      exact hPZ
    obtain ⟨Q, hQ, f, hf, hQZ⟩ := exists_supported_perfect_extension_across_affine_openImmersion
      j k hcover (T.ι ⁻¹ᵁ Z) hTZ P hP hPZ'
    refine ⟨hUS.trans le_sup_left, Q, hQ, ⟨(derivedRetractOfWeakStabilization i j r f).trans
      (Retract.ofIso ?_)⟩, hQZ⟩
    exact (toDerived U.toScheme).mapIso
      ((eqToIso (restrict_congr (X.homOfLE_homOfLE hUS
        (le_sup_left : S ≤ S ⊔ V.val)))).app Q)

/-- On an arbitrary qcqs scheme, every original perfect complex on a compact
open is a literal derived retract of the original restriction of a global
perfect complex. Only a finite affine cover is used; shift multiplicities are
allowed to grow during the actual chart-by-chart construction. -/
lemma locallyPerfect_exists_global_supported_derived_retract {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (hz : IsZero ((toDerived (U.ι ⁻¹ᵁ Z).toScheme).obj ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E))) :
    ∃ P : Complex X, locallyPerfect X P ∧
      Nonempty (Retract ((toDerived U.toScheme).obj E)
        ((toDerived U.toScheme).obj ((restrict U.ι).obj P))) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj P)) := by
  classical
  obtain ⟨s, hs, hcover⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (X := X) (U := ⊤)).mp (by simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set
      X)))
  have ht : hs.toFinset.sup (fun V => V.val) = (⊤ : X.Opens) := by
    simpa only [Finset.sup_eq_iSup, Set.Finite.mem_toFinset] using hcover.symm
  have h := exists_supported_perfect_retract_on_finite_affine_union U hU E hE Z hZ hz hs.toFinset
  rw [ht, sup_top_eq] at h
  obtain ⟨hUTop, P, hP, ⟨r⟩, hPZ⟩ := h
  let Q := (restrict X.topIso.inv).obj P
  have hj : U.ι ≫ X.topIso.inv = X.homOfLE (le_top : U ≤ ⊤) := by
    apply (cancel_mono (⊤ : X.Opens).ι).mp
    simp
  let e : (restrict U.ι).obj Q ≅ (restrict (X.homOfLE (le_top : U ≤ ⊤))).obj P :=
    (restrictCompIso U.ι X.topIso.inv ≪≫ eqToIso (restrict_congr hj)).app P
  have hQZ : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj Q)) := by
    have h := isZero_restrict_preimage_of_isZero X.topIso.inv ((⊤ : X.Opens).ι ⁻¹ᵁ Z) P hPZ
    have he : X.topIso.inv ⁻¹ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ Z) = Z := by
      change X.topIso.inv ⁻¹ᵁ (X.topIso.hom ⁻¹ᵁ Z) = Z
      rw [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage]
    rw [he] at h
    exact h
  exact ⟨Q, locallyPerfect_restrict X.topIso.inv hP,
    ⟨r.trans (Retract.ofIso ((toDerived U.toScheme).mapIso e.symm))⟩, hQZ⟩


/-- Actual perfect complements with prescribed global vanishing on a
compact open of an arbitrary qcqs scheme. -/
lemma locallyPerfect_exists_global_supported_perfect_complement {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (E : Complex U.toScheme)
    (hE : locallyPerfect U.toScheme E) (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (hz : IsZero ((toDerived (U.ι ⁻¹ᵁ Z).toScheme).obj ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E))) :
    ∃ (P : Complex X) (C : Complex U.toScheme),
      locallyPerfect X P ∧ locallyPerfect U.toScheme C ∧
      Nonempty ((toDerived U.toScheme).obj ((restrict U.ι).obj P) ≅
        (toDerived U.toScheme).obj (E ⊞ C)) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj P)) := by
  obtain ⟨P, hP, ⟨r⟩, hPZ⟩ := locallyPerfect_exists_global_supported_derived_retract U hU E hE Z hZ
    hz
  obtain ⟨C, hC, e, he⟩ := exists_actual_perfect_complement_of_derived_retract hE
    (locallyPerfect_restrict U.ι hP) r
  exact ⟨P, C, hP, hC, ⟨e⟩, hPZ⟩
lemma locallyPerfect_exists_global_supported_perfect_complement_of_openImmersion
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (E : Complex U) (hE : locallyPerfect U E)
    (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (hz : IsZero ((toDerived (j ⁻¹ᵁ Z).toScheme).obj ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ (P : Complex X) (C : Complex U), locallyPerfect X P ∧ locallyPerfect U C ∧
      Nonempty ((toDerived U).obj ((restrict j).obj P) ≅ (toDerived U).obj (E ⊞ C)) ∧
      IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj P)) := by
  let W := j.opensRange
  have hW : IsCompact (W : Set X) := isCompact_range j.continuous
  let E' := (restrict j.isoOpensRange.inv).obj E
  have hz' : IsZero ((toDerived (W.ι ⁻¹ᵁ Z).toScheme).obj ((restrict (W.ι ⁻¹ᵁ Z).ι).obj E')) := by
    have h := isZero_restrict_preimage_of_isZero j.isoOpensRange.inv (j ⁻¹ᵁ Z) E hz
    have hcomp : j.isoOpensRange.inv ≫ j = W.ι := by
      calc
        j.isoOpensRange.inv ≫ j = j.isoOpensRange.inv ≫ (j.isoOpensRange.hom ≫ W.ι) :=
          congrArg (fun t => j.isoOpensRange.inv ≫ t) j.isoOpensRange_hom_ι.symm
        _ = W.ι := by simp
    rw [← Scheme.Hom.comp_preimage, hcomp] at h
    exact h
  obtain ⟨P, C', hP, hC', ⟨e⟩, hPZ⟩ := locallyPerfect_exists_global_supported_perfect_complement W
    hW E'
    (locallyPerfect_restrict j.isoOpensRange.inv hE) Z hZ hz'
  let C := (restrict j.isoOpensRange.hom).obj C'
  let eleft : (restrict j).obj P ≅ (restrict j.isoOpensRange.hom).obj ((restrict W.ι).obj P) :=
    ((restrictCompIso j.isoOpensRange.hom W.ι ≪≫
      eqToIso (restrict_congr j.isoOpensRange_hom_ι)).symm).app P
  let eE : (restrict j.isoOpensRange.hom).obj E' ≅ E :=
    (restrictCompIso j.isoOpensRange.hom j.isoOpensRange.inv ≪≫
      eqToIso (restrict_congr j.isoOpensRange.hom_inv_id) ≪≫ restrictIdIso U).app E
  let : PreservesBinaryBiproducts (restrict j.isoOpensRange.hom) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eright := (restrict j.isoOpensRange.hom).mapBiprod E' C' ≪≫ biprod.mapIso eE (Iso.refl C)
  exact ⟨P, C, hP, locallyPerfect_restrict j.isoOpensRange.hom hC',
    ⟨(toDerived U).mapIso eleft ≪≫ restrictDerivedIso j.isoOpensRange.hom e ≪≫
      (toDerived U).mapIso eright⟩, hPZ⟩

end Quillen.PerfectComplexes
