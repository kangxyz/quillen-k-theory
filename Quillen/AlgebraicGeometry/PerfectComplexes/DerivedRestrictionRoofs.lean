/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Roofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionIso

/-! # Derived roof transport along an original scheme isomorphism

The original normalized derived restriction is injective along an isomorphism,
and actual quasi-isomorphisms are reflected. These facts transport the genuine
roof condition through an isomorphic source scheme while retaining both global
chain arrows and the original local derived square.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes

/-- Original normalized restriction reflects equality along a scheme isomorphism. -/
lemma restrictDerivedHom_injective_of_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsIso j] [IsOpenImmersion j] {K L : Complex X} :
    Function.Injective (restrictDerivedHom j (K := K) (L := L)) := by
  intro φ ψ h
  apply (derivedRestrict j).map_injective
  apply (cancel_epi ((derivedRestrictFactors j).inv.app K)).mp
  apply (cancel_mono ((derivedRestrictFactors j).hom.app L)).mp
  simpa only [restrictDerivedHom, Category.assoc] using h

/-- Actual complex restriction reflects quasi-isomorphisms along a scheme isomorphism. -/
lemma quasiIso_restrict_iff_of_isIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsIso j] [IsOpenImmersion j] {K L : Complex X} (f : K ⟶ L) :
    QuasiIso ((restrict j).map f) ↔ QuasiIso f := by
  let : (Scheme.Modules.restrictFunctor j).IsEquivalence :=
    (moduleRestrictEquivalenceOfIso (asIso j)).isEquivalence_functor
  exact quasiIso_map_iff_of_preservesHomology f (Scheme.Modules.restrictFunctor j)

namespace OpenDerivedImage

/-- Transport through a genuine source scheme isomorphism preserves both
original roof arrows and reflects the original local derived equation. -/
lemma hasDerivedRoofs_of_sourceIso {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (e : V ≅ U) (h : e.hom ≫ j = k) (hk : HasDerivedRoofs k) :
    HasDerivedRoofs j := by
  let c : restrict j ⋙ restrict e.hom ≅ restrict k :=
    restrictCompIso e.hom j ≪≫ eqToIso (restrict_congr h)
  intro A B hA hB α
  let Q := toDerived V
  let α' := Q.map (c.inv.app A) ≫ restrictDerivedHom e.hom α ≫ Q.map (c.hom.app B)
  obtain ⟨M, q, g, hM, hq, hg⟩ := hk A B hA hB α'
  have hq' : QuasiIso ((restrict e.hom).map ((restrict j).map q)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app M) (c.app A) (c.hom.naturality q).symm)).mpr hq
  refine ⟨M, q, g, hM, (quasiIso_restrict_iff_of_isIso e.hom _).mp hq', ?_⟩
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
  have hα : restrictDerivedHom e.hom α ≫ Q.map (c.hom.app B) =
      Q.map (c.hom.app A) ≫ α' := by
    dsimp only [α']
    rw [← Category.assoc, ← Q.map_comp, c.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hα, ← Category.assoc, hqnat, Category.assoc, hg, hgnat]

end OpenDerivedImage
end Quillen.PerfectComplexes
