/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.ModulePerfectClosure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedModuleReplacement
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Affine.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# Principal localization of finite-projective derived models

The actual derived restriction image is triangulated. For termwise quasicoherent targets it is exactly the existence of the original strict restriction quasi-isomorphism.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- The actual derived image of original-ring bounded finite-projective module
complexes under principal localization. -/
def principalModuleDerivedImage (R : CommRingCat.{u}) (r : R) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} (Localization.Away r))) := fun K =>
  ∃ P : ModuleComplex R, moduleStrictPerfect R P ∧
    Nonempty (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P) ≅ K)

instance (R : CommRingCat.{u}) (r : R) :
    (principalModuleDerivedImage R r).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance (R : CommRingCat.{u}) (r : R) :
    (principalModuleDerivedImage R r).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro K ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, moduleStrictPerfect_shift R hP n,
      ⟨DerivedCategory.Q.mapIso (((localize r (.up ℤ)).commShiftIso n).app P) ≪≫
        (DerivedCategory.Q.commShiftIso n).app ((localize r (.up ℤ)).obj P) ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

/-- Clearing the actual connecting morphism's denominator makes the original
principal image closed under the original distinguished cone triangles. -/
instance (R : CommRingCat.{u}) (r : R) :
    (principalModuleDerivedImage R r).IsTriangulatedClosed₃ :=
  .mk' (by
    rintro T hT ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
    let L := localize r (.up ℤ)
    let α := eP.hom ≫ T.mor₁ ≫ eK.inv
    obtain ⟨n, g, hn, hg⟩ := exists_principal_derived_module_fraction R r hP α
    have : IsIso (DerivedCategory.Q.map (L.map (r ^ n • 𝟙 P))) := inferInstance
    let eP' := asIso (DerivedCategory.Q.map (L.map (r ^ n • 𝟙 P))) ≪≫ eP
    refine ⟨CochainComplex.mappingCone g, moduleStrictPerfect_mappingCone R hP hK g, ⟨?_⟩⟩
    refine DerivedCategory.Q.mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso g
        (ModuleCat.localizedModuleFunctor (Submonoid.powers r))) ≪≫ ?_
    exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
      (DerivedCategory.mappingCone_triangle_distinguished (L.map g)) hT eP' eK (by
        change DerivedCategory.Q.map (L.map g) ≫ eK.hom = _
        rw [← hg]
        simp only [α, eP', Iso.trans_hom, asIso_hom, Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
        rfl)) )

instance (R : CommRingCat.{u}) (r : R) :
    (principalModuleDerivedImage R r).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃

/-- For actual QC target complexes, the principal derived module image agrees
with a genuine one-arrow weak restriction witness from an original strict
complex. Both directions retain the original affine reconstruction. -/
lemma exists_principal_strict_quasiIso_iff_moduleDerivedImage
    (R : CommRingCat.{u}) (r : R)
    (B : CochainComplex (Spec (.of (Localization.Away r))).Modules ℤ)
    (hB : ∀ i, (B.X i).IsQuasicoherent) :
    (∃ (E : StrictPerfect (Spec R))
      (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        B), QuasiIso q) ↔
      principalModuleDerivedImage R r
        (DerivedCategory.Q.obj ((sectionsComplex (.of (Localization.Away r))).obj B)) := by
  let S := CommRingCat.of (Localization.Away r)
  let L := localize r (.up ℤ)
  let G := associatedComplex S
  let J := restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
  let T := (sectionsComplex S).obj B
  let eB : G.obj T ≅ B := associatedSectionsIsoOfQuasicoherent S B hB
  let e := principalRestrictionAssociatedComplexIso R r
  constructor
  · rintro ⟨E, q, hq⟩
    let N := (sectionsComplex R).obj E.obj
    let eE : (associatedComplex R).obj N ≅ E.obj := associatedSectionsIso R E.property
    let uE : G.obj (L.obj N) ≅ J.obj E.obj := e.app N ≪≫ J.mapIso eE
    let : G.Full := associatedComplex_full S
    obtain ⟨qM, hqM⟩ := G.map_surjective (uE.hom ≫ q ≫ eB.inv)
    have : QuasiIso (G.map qM) := by rw [hqM]; infer_instance
    have : QuasiIso qM := (quasiIso_associated_iff S qM).mp inferInstance
    exact ⟨N, moduleStrictPerfect_sections R E.property, ⟨asIso (DerivedCategory.Q.map qM)⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    have : CochainComplex.IsKProjective (L.obj P) :=
      isKProjective_of_moduleStrictPerfect S (moduleStrictPerfect_localize R r hP)
    obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective eP.hom
    have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
    have : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mp inferInstance
    have : QuasiIso (G.map f) := (quasiIso_associated_iff S f).mpr inferInstance
    exact ⟨⟨(associatedComplex R).obj P, strictPerfect_associated R hP⟩,
      (e.app P).inv ≫ G.map f ≫ eB.hom, inferInstance⟩

end Quillen.PerfectComplexes.Affine

end

end
