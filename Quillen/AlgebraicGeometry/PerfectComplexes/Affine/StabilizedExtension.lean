/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Algebra.Homology.ProjectorCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectComplement
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

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

open AlgebraicGeometry.Scheme.Modules.Complex



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
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) (C E : CochainComplex W.toScheme.Modules ℤ)
    (e : (DerivedCategory.Q (C := W.toScheme.Modules)).obj
      ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
      (DerivedCategory.Q (C := W.toScheme.Modules)).obj (C ⊞ E)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t g : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      (DerivedCategory.Q (C := W.toScheme.Modules)).map
        ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        (DerivedCategory.Q (C := W.toScheme.Modules)).map
          ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
          (DerivedCategory.Q (C := W.toScheme.Modules)).map (biprod.map (𝟙 C) (0 : E ⟶ E)) ∧
      moduleStrictPerfect R (CochainComplex.mappingCone g) ∧
      ∃ eCone : (DerivedCategory.Q (C := W.toScheme.Modules)).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (DerivedCategory.Q (C := W.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧),
        (DerivedCategory.Q (C := W.toScheme.Modules)).map ((restrict W.ι).map
          ((associatedComplex R).map (CochainComplex.mappingCone.inr g))) ≫ eCone.hom =
            e.hom ≫ (DerivedCategory.Q (C := W.toScheme.Modules)).map
              ((biprod.snd : C ⊞ E ⟶ E) ≫ (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧)) := by
  let p : C ⊞ E ⟶ C ⊞ E := biprod.map (𝟙 C) (0 : E ⟶ E)
  let α := e.hom ≫ (DerivedCategory.Q (C := W.toScheme.Modules)).map p ≫ e.inv
  obtain ⟨P', hP', t, g, ht, hsq⟩ := exists_quasiCompact_open_strict_module_roof R W hW hP hP α
  have heq : (DerivedCategory.Q (C := W.toScheme.Modules)).map
    ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
      (DerivedCategory.Q (C := W.toScheme.Modules)).map
        ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom ≫
        (DerivedCategory.Q (C := W.toScheme.Modules)).map p := by
    rw [← hsq]
    simp [α, Category.assoc]
  refine ⟨P', hP', t, g, ht, heq, moduleStrictPerfect_mappingCone R hP' hP g, ?_⟩
  let T := (DerivedCategory.Q (C := W.toScheme.Modules)).mapTriangle.obj
    (CochainComplex.mappingCone.triangle
    ((restrict W.ι).map ((associatedComplex R).map g)))
  let T' := (DerivedCategory.Q (C := W.toScheme.Modules)).mapTriangle.obj
    (CochainComplex.mappingCone.triangle p)
  let et := isoTriangleOfIso₁₂ T T'
    (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _)
    (asIso ((DerivedCategory.Q (C := W.toScheme.Modules)).map
      ((restrict W.ι).map ((associatedComplex R).map t))) ≪≫ e) e
      (by
      change (DerivedCategory.Q (C := W.toScheme.Modules)).map
        ((restrict W.ι).map ((associatedComplex R).map g)) ≫ e.hom =
        ((DerivedCategory.Q (C := W.toScheme.Modules)).map
          ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom) ≫
          (DerivedCategory.Q (C := W.toScheme.Modules)).map p
      simpa only [Category.assoc] using heq)
  let ec := (DerivedCategory.Q (C := W.toScheme.Modules)).mapIso (openAssociatedConeIso R W.ι g) ≪≫
    Triangle.π₃.mapIso et ≪≫ Quillen.CochainComplex.projectorConeDerivedIso C E
  refine ⟨ec, ?_⟩
  have hcomm := et.hom.comm₂
  change (DerivedCategory.Q (C := W.toScheme.Modules)).map (CochainComplex.mappingCone.inr
      ((restrict W.ι).map ((associatedComplex R).map g))) ≫ (Triangle.π₃.mapIso et).hom =
        e.hom ≫ (DerivedCategory.Q (C := W.toScheme.Modules)).map
          (CochainComplex.mappingCone.inr p) at hcomm
  dsimp only [ec, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← (DerivedCategory.Q (C := W.toScheme.Modules)).map_comp,
    openAssociatedConeIso_inr]
  erw [hcomm]
  rw [Category.assoc]
  exact congrArg (fun z => e.hom ≫ z) (Quillen.CochainComplex.projectorConeDerivedIso_inr C E)

/-- Every original perfect complex on a qc affine open, stabilized by its
positive shift, is the restriction of an actual global finite-projective cone. -/
lemma locallyPerfect_exists_stabilized_extension_cone (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : CochainComplex W.toScheme.Modules ℤ) (hE : locallyPerfect W.toScheme E) :
    ∃ (P P' : ModuleComplex R) (_ : moduleStrictPerfect R P) (_ : moduleStrictPerfect R P')
      (g : P' ⟶ P), moduleStrictPerfect R (CochainComplex.mappingCone g) ∧
      Nonempty ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (DerivedCategory.Q (C := W.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨K, P, n, hP, f, eK, hn, hM, hC, hz, e, he⟩ :=
    locallyPerfect_exists_actual_perfect_complement R W hW E hE 0
  obtain ⟨P', hP', t, g, ht, hsq, hg, eg, heg⟩ :=
    exists_stabilized_extension_cone_of_complement R W hW hP _ E e
  exact ⟨P, P', hP, hP', g, hg, ⟨eg⟩⟩

/-- The extension may be chosen globally strict-perfect; the endpoint retains
the original all-sheaf E and the literal complex biproduct with E[1]. -/
lemma locallyPerfect_exists_global_strict_stabilized_extension (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : CochainComplex W.toScheme.Modules ℤ) (hE : locallyPerfect W.toScheme E) :
    ∃ (Q : CochainComplex (Spec R).Modules ℤ), strictPerfect (Spec R) Q ∧
      Nonempty ((DerivedCategory.Q (C := W.toScheme.Modules)).obj ((restrict W.ι).obj Q) ≅
        (DerivedCategory.Q (C := W.toScheme.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨P, P', hP, hP', g, hg, eg⟩ := locallyPerfect_exists_stabilized_extension_cone R W hW E hE
  exact ⟨(associatedComplex R).obj (CochainComplex.mappingCone g), strictPerfect_associated R hg,
    eg⟩

end Quillen.PerfectComplexes.Affine
