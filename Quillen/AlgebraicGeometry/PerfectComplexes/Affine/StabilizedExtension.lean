/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.ProjectorCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectComplement

/-!
# Actual stabilized extensions from quasi-compact affine opens

For every original locally-perfect all-sheaf complex E on a quasi-compact
open W of Spec R, the literal E plus E shifted by the integer 1 is the
restriction, in the original derived category, of a global strict-perfect
complex. The extension is explicitly associated to the actual mapping cone
of a map between genuine bounded finite-projective module complexes.

The construction takes the proved original complement, lifts its projector
through the genuine qc-open finite-perfect denominator roof, and compares
the two original cone triangles. The helper retains both the exact projector
square and the original cone-inclusion equation. All commutative rings and
empty opens are included. No direct strict-to-E chain quasi-isomorphism is
asserted for an arbitrary all-sheaf E.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Lift the genuine complement projector through an actual locally weak
finite-projective denominator. Its literal global numerator cone extends the
original E plus its positive integer shift. -/
lemma exists_stabilized_extension_cone_of_complement (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) (C E : Complex W.toScheme)
    (e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
      (toDerived W.toScheme).obj (C ⊞ E)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t g : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
          (toDerived W.toScheme).map (biprod.map (𝟙 C) (0 : E ⟶ E)) ∧
      moduleStrictPerfect R (CochainComplex.mappingCone g) ∧
      ∃ eCone : (toDerived W.toScheme).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧),
        (toDerived W.toScheme).map ((restrict W.ι).map
          ((associatedComplex R).map (CochainComplex.mappingCone.inr g))) ≫ eCone.hom =
            e.hom ≫ (toDerived W.toScheme).map
              ((biprod.snd : C ⊞ E ⟶ E) ≫ (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧)) := by
  let p : C ⊞ E ⟶ C ⊞ E := biprod.map (𝟙 C) (0 : E ⟶ E)
  let α := e.hom ≫ (toDerived W.toScheme).map p ≫ e.inv
  obtain ⟨P', hP', t, g, ht, hsq⟩ := exists_quasiCompact_open_strict_module_roof R W hW hP hP α
  have heq : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
        (toDerived W.toScheme).map p := by
    rw [← hsq]
    simp [α, Category.assoc]
  refine ⟨P', hP', t, g, ht, heq, moduleStrictPerfect_mappingCone R hP' hP g, ?_⟩
  let T := (toDerived W.toScheme).mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((restrict W.ι).map ((associatedComplex R).map g)))
  let T' := (toDerived W.toScheme).mapTriangle.obj (CochainComplex.mappingCone.triangle p)
  let et := isoTriangleOfIso₁₂ T T'
    (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _)
    (asIso ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t))) ≪≫ e) e
      (by
      change (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom) ≫
          (toDerived W.toScheme).map p
      simpa only [Category.assoc] using heq)
  let ec := (toDerived W.toScheme).mapIso (openAssociatedConeIso R W.ι g) ≪≫
    Triangle.π₃.mapIso et ≪≫ Quillen.CochainComplex.projectorConeDerivedIso C E
  refine ⟨ec, ?_⟩
  have hcomm := et.hom.comm₂
  change (toDerived W.toScheme).map (CochainComplex.mappingCone.inr
      ((restrict W.ι).map ((associatedComplex R).map g))) ≫ (Triangle.π₃.mapIso et).hom =
        e.hom ≫ (toDerived W.toScheme).map (CochainComplex.mappingCone.inr p) at hcomm
  dsimp only [ec, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← (toDerived W.toScheme).map_comp,
    openAssociatedConeIso_inr]
  erw [hcomm]
  rw [Category.assoc]
  exact congrArg (fun z => e.hom ≫ z) (Quillen.CochainComplex.projectorConeDerivedIso_inr C E)

/-- Every original perfect complex on a qc affine open, stabilized by its
positive shift, is the restriction of an actual global finite-projective cone. -/
lemma locallyPerfect_exists_stabilized_extension_cone (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ (P P' : ModuleComplex R) (_ : moduleStrictPerfect R P) (_ : moduleStrictPerfect R P')
      (g : P' ⟶ P), moduleStrictPerfect R (CochainComplex.mappingCone g) ∧
      Nonempty ((toDerived W.toScheme).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨K, P, n, hP, f, eK, hn, hM, hC, hz, e, he⟩ :=
    locallyPerfect_exists_actual_perfect_complement R W hW E hE 0
  obtain ⟨P', hP', t, g, ht, hsq, hg, eg, heg⟩ :=
    exists_stabilized_extension_cone_of_complement R W hW hP _ E e
  exact ⟨P, P', hP, hP', g, hg, ⟨eg⟩⟩

/-- The extension may be chosen globally strict-perfect; the endpoint retains
the original all-sheaf E and the literal complex biproduct with E[1]. -/
lemma locallyPerfect_exists_global_strict_stabilized_extension (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) :
    ∃ (Q : Complex (Spec R)), strictPerfect (Spec R) Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj Q) ≅
        (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨P, P', hP, hP', g, hg, eg⟩ := locallyPerfect_exists_stabilized_extension_cone R W hW E hE
  exact ⟨(associatedComplex R).obj (CochainComplex.mappingCone g), strictPerfect_associated R hg,
    eg⟩

end Quillen.PerfectComplexes.Affine
