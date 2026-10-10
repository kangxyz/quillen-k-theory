/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Affine.DerivedModuleReplacement
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Quillen.Algebra.Homology.DerivedCategory.BoundedComparison

/-!
# Actual derived closure of bounded finite-projective module models

Single finite-projective modules, shifts, and literal mapping cones are
bounded finite-projective complexes. K-projective chain representatives and
the original distinguished triangles prove extension closure of their actual
derived essential image. This image is an existential statement about genuine
complexes and original derived isomorphisms, with every closure law proved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex TopologicalSpace

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard

/-- A finite-projective module in any single degree is a bounded finite-projective complex. -/
lemma moduleStrictPerfect_single (R : CommRingCat.{u}) (n : ℤ) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] :
    moduleStrictPerfect R ((CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj M) := by
  refine ⟨⟨n, n, fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩, fun i => ?_⟩
  by_cases hi : i = n
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (.up ℤ) n M).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) n M i hi
    let :=  ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, inferInstance⟩

/-- The actual cochain shift preserves bounded finite-projective terms. -/
lemma moduleStrictPerfect_shift (R : CommRingCat.{u}) {K : ModuleComplex R}
    (hK : moduleStrictPerfect R K) (n : ℤ) : moduleStrictPerfect R (K⟦n⟧) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨a - n, b - n, fun i hi => ?_⟩, fun i => ?_⟩
  · exact (hb (i + n) (by omega)).of_iso (K.shiftFunctorObjXIso n i (i+n) rfl)
  · let :=  (hp (i+n)).1
    let :=  (hp (i+n)).2
    let e := (K.shiftFunctorObjXIso n i (i+n) rfl).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- The literal mapping cone of finite-projective bounded complexes is again bounded finite-projective. -/
lemma moduleStrictPerfect_mappingCone (R : CommRingCat.{u}) {P K : ModuleComplex R}
    (hP : moduleStrictPerfect R P) (hK : moduleStrictPerfect R K) (f : P ⟶ K) :
    moduleStrictPerfect R (CochainComplex.mappingCone f) := by
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hP
  obtain ⟨⟨c, d, hd⟩, hk⟩ := hK
  refine ⟨⟨min (a-1) c, max (b-1) d, fun i hi => ?_⟩, fun i => ?_⟩
  · rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hb (i+1) (by omega), hd i (by omega)⟩
  · let :=  (hp (i+1)).1
    let :=  (hp (i+1)).2
    let :=  (hk i).1
    let :=  (hk i).2
    let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i+1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- A genuine derived target model and a finite-projective source give a genuine finite-projective model of the original cone. -/
lemma exists_moduleStrictPerfect_cone_model (R : CommRingCat.{u})
    {P K L : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hL : moduleStrictPerfect R L) (f : P ⟶ K)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ (C : ModuleComplex R), moduleStrictPerfect R C ∧
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone f) ≅ DerivedCategory.Q.obj C) := by
  have := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨g, hg⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective
    (DerivedCategory.Q.map f ≫ e.hom)
  refine ⟨CochainComplex.mappingCone g, moduleStrictPerfect_mappingCone R hP hL g, ⟨?_⟩⟩
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) (Iso.refl _) e (by simpa using hg.symm))

/-- The actual essential image of bounded finite-projective module complexes. -/
def finiteProjectiveDerivedObjects (R : CommRingCat.{u}) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) := fun K =>
  ∃ P : ModuleComplex R, moduleStrictPerfect R P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K)

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro K ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, moduleStrictPerfect_shift R hP n,
      ⟨(DerivedCategory.Q.commShiftIso n).app P ≪≫ (shiftFunctor _ n).mapIso eP⟩⟩⟩

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).IsTriangulatedClosed₃ :=
  .mk' (by
    rintro T hT ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
    have := isKProjective_of_moduleStrictPerfect R hP
    obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective
      (eP.hom ≫ T.mor₁ ≫ eK.inv)
    refine ⟨CochainComplex.mappingCone f, moduleStrictPerfect_mappingCone R hP hK f, ⟨?_⟩⟩
    exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
      (DerivedCategory.mappingCone_triangle_distinguished f) hT eP eK (by
        change DerivedCategory.Q.map f ≫ eK.hom = _
        rw [hf]
        simp)))

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃

end Quillen.PerfectComplexes.Affine
