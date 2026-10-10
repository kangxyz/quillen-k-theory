/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedImageRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality

/-! # Genuine roofs for arbitrary compact open immersions into affine schemes

The original affine-open roof theorem is transported first through the actual
open-image isomorphism and then through the affine scheme's spectrum
isomorphism. Actual global numerators and denominators remain unchanged at
the stated endpoints; no presentation of the affine scheme is supplied.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage

/-- The original affine-open theorem applies to every compact open immersion
into a spectrum, rather than only the chosen opens inclusion. -/
lemma spec_hasDerivedRoofs_of_compact {U : Scheme.{u}} (R : CommRingCat.{u})
    (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U] : HasDerivedRoofs j := by
  apply hasDerivedRoofs_of_sourceIso j j.opensRange.ι j.isoOpensRange.symm
    j.isoOpensRange_inv_comp
  exact affine_hasDerivedRoofs R j.opensRange (isCompact_range j.continuous)

/-- Actual roofs for compact open immersions into any affine scheme. The
scheme presentation is eliminated by genuine restriction equivalences and
original globally weak model fractions. -/
lemma affine_hasDerivedRoofs_of_compact {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace U] [IsAffine X] :
    HasDerivedRoofs j := by
  let i := X.isoSpec.hom
  let k := j ≫ i
  have hk : HasDerivedRoofs k := spec_hasDerivedRoofs_of_compact _ k
  let models : ObjectProperty (Complex X) := fun A =>
    ∃ P : Complex (Spec Γ(X, ⊤)),
      locallyPerfect _ P ∧ A = (restrict i).obj P
  apply hasDerivedRoofs_of_models j models
  · intro A hA
    let P := (restrict X.isoSpec.inv).obj A
    let e : (restrict i).obj P ≅ A :=
      (restrictCompIso i X.isoSpec.inv ≪≫
        eqToIso (restrict_congr X.isoSpec.hom_inv_id) ≪≫ restrictIdIso X).app A
    exact ⟨(restrict i).obj P,
      ⟨P, locallyPerfect_restrict X.isoSpec.inv hA, rfl⟩, ⟨(toDerived X).mapIso e⟩⟩
  · rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ α
    let Q := toDerived U
    let c := restrictCompIso j i
    let α' := Q.map (c.inv.app A) ≫ α ≫ Q.map (c.hom.app B)
    obtain ⟨M, q, g, hM, hq, hg⟩ := hk A B hA hB α'
    refine ⟨(restrict i).obj M, (restrict i).map q, (restrict i).map g,
      locallyPerfect_restrict i hM, ?_, ?_⟩
    · exact (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (c.app M) (c.app A) (c.hom.naturality q).symm)).mpr hq
    · apply (cancel_mono (Q.map (c.hom.app B))).mp
      rw [Category.assoc]
      change Q.map ((restrict i ⋙ restrict j).map q) ≫ α ≫ Q.map (c.hom.app B) =
        Q.map ((restrict i ⋙ restrict j).map g) ≫ Q.map (c.hom.app B)
      have hqnat := congrArg Q.map (c.hom.naturality q)
      have hgnat := congrArg Q.map (c.hom.naturality g)
      simp only [Functor.map_comp] at hqnat hgnat
      have hα : α ≫ Q.map (c.hom.app B) = Q.map (c.hom.app A) ≫ α' := by
        dsimp only [α']
        rw [← Category.assoc, ← Q.map_comp, c.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
      rw [hα, ← Category.assoc, hqnat, Category.assoc, hg, hgnat]

end Quillen.PerfectComplexes.OpenDerivedImage
