/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.Homology.DerivedCategory.BoundedComparison
import Quillen.PerfectComplexes.Affine.DerivedSingleComparison
import Quillen.PerfectComplexes.Homology

/-!
# The bounded affine derived equivalence

Over any commutative ring, the original `associatedDerived` functor is fully
faithful on cohomologically bounded objects. Its bounded essential image is
exactly the cohomologically bounded part of the ambient derived category of
all module sheaves with quasicoherent homology. The displayed equivalence
retains the original forward functor and map, definitionally after inclusion.

Every such sheaf-derived object has a module chain representative with the
same requested lower and upper term bounds. In particular an affine locally
perfect complex has a bounded module representative, without termwise QC
hypotheses on the original complex. Finite-projective strictification and an
unbounded derived equivalence are separate theorems and are not asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
universe u
open AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- The original derived map is bijective between any two cohomologically bounded module objects. -/
lemma associatedDerived_bounded_map_bijective (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b c d : ℤ)
    [K.IsGE a] [K.IsLE b] [L.IsGE c] [L.IsLE d] :
    Function.Bijective ((associatedDerived R).map : (K ⟶ L) → _) :=
  DerivedHomComparison.bounded_map_bijective_of_single_zero_shift (associatedDerived R)
    (associatedDerived_single_int_shift_map_bijective R) K L a b c d

end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

abbrev associatedBoundedDerived (R : CommRingCat.{u}) :
    DerivedCategory.Bounded (ModuleCat.{u} R) ⥤ Derived (Spec R) :=
  DerivedCategory.Bounded.ι ⋙ associatedDerived R

instance (R : CommRingCat.{u}) : (associatedBoundedDerived R).Full where
  map_surjective {X Y} f := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := Y.property
    obtain ⟨g, hg⟩ := (associatedDerived_bounded_map_bijective R X.obj Y.obj a b c d).surjective f
    exact ⟨ObjectProperty.homMk g, hg⟩

instance (R : CommRingCat.{u}) : (associatedBoundedDerived R).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := Y.property
    apply ObjectProperty.hom_ext
    exact (associatedDerived_bounded_map_bijective R X.obj Y.obj a b c d).injective h


end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma associatedBoundedDerived_essImage_single (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℤ) :
    (associatedBoundedDerived R).essImage ((DerivedCategory.singleFunctor (Spec R).Modules n).obj M) := by
  let A := moduleSpecΓFunctor.obj M
  refine ⟨⟨(DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj A,
    ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩⟩, ⟨?_⟩⟩
  exact ((tilde.functor R).mapDerivedCategorySingleFunctor n).app A ≪≫
    (DerivedCategory.singleFunctor (Spec R).Modules n).mapIso (asIso M.fromTildeΓ)

/-- Bounded QC homology suffices for reconstruction in the ambient derived category of all sheaves. -/
lemma associatedBoundedDerived_essImage_of_quasicoherent_homology
    (R : CommRingCat.{u}) (K : Derived (Spec R)) (a b : ℤ) [DerivedCategory.IsGE (C := (Spec R).Modules) K a] [DerivedCategory.IsLE (C := (Spec R).Modules) K b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K).IsQuasicoherent) :
    (associatedBoundedDerived R).essImage K := by
  let : (associatedBoundedDerived R).essImage.IsTriangulatedClosed₂ :=
    (inferInstance : (associatedBoundedDerived R).essImage.IsTriangulated).toIsTriangulatedClosed₂
  let Q : ObjectProperty (Spec R).Modules := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let : Q.IsClosedUnderIsomorphisms :=
    inferInstanceAs ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderIsomorphisms)
  apply DerivedHomComparison.property_of_bounded_homology_single_generation
    (C := (Spec R).Modules) (associatedBoundedDerived R).essImage Q _ _ K a b hK
  · exact Q.prop_of_iso (tilde.functor R).mapZeroObject inferInstance
  · intro M hM n
    have : M.IsQuasicoherent := hM
    exact associatedBoundedDerived_essImage_single R M n


/-- The bounded essential image is exactly bounded quasicoherent homology, over any ring. -/
lemma associatedBoundedDerived_essImage_iff (R : CommRingCat.{u}) (K : Derived (Spec R)) :
    (associatedBoundedDerived R).essImage K ↔
      (∃ a : ℤ, DerivedCategory.IsGE (C := (Spec R).Modules) K a) ∧
      (∃ b : ℤ, DerivedCategory.IsLE (C := (Spec R).Modules) K b) ∧
      ∀ i, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K).IsQuasicoherent := by
  constructor
  · rintro ⟨A, ⟨e⟩⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := A.property
    have : DerivedCategory.IsGE (C := (Spec R).Modules) ((associatedBoundedDerived R).obj A) a :=
      inferInstanceAs (((tilde.functor R).mapDerivedCategory.obj A.obj).IsGE a)
    have : DerivedCategory.IsLE (C := (Spec R).Modules) ((associatedBoundedDerived R).obj A) b :=
      inferInstanceAs (((tilde.functor R).mapDerivedCategory.obj A.obj).IsLE b)
    refine ⟨⟨a, DerivedCategory.TStructure.t.isGE_of_iso e a⟩,
      ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩, fun i => ?_⟩
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso e)
      (associatedDerived_quasicoherent_homology R A.obj i)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hK⟩
    exact associatedBoundedDerived_essImage_of_quasicoherent_homology R K a b hK


/-- The actual bounded, quasicoherent-homology part of the ambient derived category. -/
def boundedQuasicoherentObjects (R : CommRingCat.{u}) : ObjectProperty (Derived (Spec R)) :=
  fun K => (∃ a : ℤ, DerivedCategory.IsGE (C := (Spec R).Modules) K a) ∧
    (∃ b : ℤ, DerivedCategory.IsLE (C := (Spec R).Modules) K b) ∧
    ∀ i, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K).IsQuasicoherent


lemma associatedBoundedDerived_essImage_eq (R : CommRingCat.{u}) :
    (associatedBoundedDerived R).essImage = boundedQuasicoherentObjects R := by
  funext K
  exact propext (associatedBoundedDerived_essImage_iff R K)

instance (R : CommRingCat.{u}) : (boundedQuasicoherentObjects R).IsClosedUnderIsomorphisms := by
  rw [← associatedBoundedDerived_essImage_eq R]
  infer_instance

instance (R : CommRingCat.{u}) : (boundedQuasicoherentObjects R).IsTriangulated := by
  rw [← associatedBoundedDerived_essImage_eq R]
  infer_instance

abbrev BoundedQuasicoherentDerived (R : CommRingCat.{u}) :=
  (boundedQuasicoherentObjects R).FullSubcategory

/-- The original affine comparison, with source and target restricted to the proved bounded parts. -/
def associatedBoundedQuasicoherent (R : CommRingCat.{u}) :
    DerivedCategory.Bounded (ModuleCat.{u} R) ⥤ BoundedQuasicoherentDerived R :=
  (boundedQuasicoherentObjects R).lift (associatedBoundedDerived R)
    (fun A => (associatedBoundedDerived_essImage_iff R _).mp ⟨A, ⟨Iso.refl _⟩⟩)


instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).CommShift ℤ := by
  dsimp only [associatedBoundedQuasicoherent]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).IsTriangulated := by
  dsimp only [associatedBoundedQuasicoherent]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).Full :=
  inferInstanceAs ((boundedQuasicoherentObjects R).lift (associatedBoundedDerived R) _).Full

instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).Faithful :=
  inferInstanceAs ((boundedQuasicoherentObjects R).lift (associatedBoundedDerived R) _).Faithful

instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).EssSurj where
  mem_essImage K := by
    obtain ⟨A, ⟨e⟩⟩ := (associatedBoundedDerived_essImage_iff R K.obj).mpr K.property
    exact ⟨A, ⟨ObjectProperty.isoMk (boundedQuasicoherentObjects R) e⟩⟩

instance (R : CommRingCat.{u}) : (associatedBoundedQuasicoherent R).IsEquivalence where

/-- Bounded affine derived comparison, over any commutative ring. -/
def boundedDerivedEquivalence (R : CommRingCat.{u}) :
    DerivedCategory.Bounded (ModuleCat.{u} R) ≌ BoundedQuasicoherentDerived R :=
  (associatedBoundedQuasicoherent R).asEquivalence

@[simp]
lemma boundedDerivedEquivalence_functor_map (R : CommRingCat.{u})
    {K L : DerivedCategory.Bounded (ModuleCat.{u} R)} (f : K ⟶ L) :
    ((boundedDerivedEquivalence R).functor.map f).hom = (associatedDerived R).map f.hom := rfl

/-- Forgetting the bounded target recovers the original comparison, definitionally. -/
def boundedDerivedEquivalenceFactors (R : CommRingCat.{u}) :
    (boundedDerivedEquivalence R).functor ⋙ (boundedQuasicoherentObjects R).ι ≅
      DerivedCategory.Bounded.ι ⋙ associatedDerived R := Iso.refl _

/-- Reconstruct a module complex with the exact requested term bounds and an actual original-localization isomorphism. -/
lemma exists_bounded_module_representative_of_quasicoherent_homology
    (R : CommRingCat.{u}) (K : Derived (Spec R)) (a b : ℤ)
    [DerivedCategory.IsGE (C := (Spec R).Modules) K a]
    [DerivedCategory.IsLE (C := (Spec R).Modules) K b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K).IsQuasicoherent) :
    ∃ (L : ModuleComplex R), L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj L) ≅ K) := by
  obtain ⟨A, ⟨e⟩⟩ := associatedBoundedDerived_essImage_of_quasicoherent_homology R K a b hK
  have hga := (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isGE_of_iso e.symm a
  have hla := (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isLE_of_iso e.symm b
  have : A.obj.IsGE a :=
    (DerivedHomComparison.mapDerivedCategory_isGE_iff (tilde.functor R) A.obj a).mp hga
  have : A.obj.IsLE b :=
    (DerivedHomComparison.mapDerivedCategory_isLE_iff (tilde.functor R) A.obj b).mp hla
  obtain ⟨L, hLge, hLle, ⟨eL⟩⟩ := A.obj.exists_iso_Q_obj_of_isGE_of_isLE a b
  exact ⟨L, hLge, hLle, ⟨((associatedDerivedFactors R).app L).symm ≪≫
    (associatedDerived R).mapIso eL.symm ≪≫ e⟩⟩

/-- An affine locally-perfect complex has a bounded module representative. Finite projectivity of the representative is not asserted. -/
lemma locallyPerfect_exists_bounded_module_representative (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K) :
    ∃ (L : ModuleComplex R) (a b : ℤ), L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj L) ≅
        (toDerived (Spec R)).obj K) := by
  obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded hK
  have : K.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hab i (Or.inl hi)
  have : K.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hab i (Or.inr hi)
  have : DerivedCategory.IsGE (C := (Spec R).Modules) ((toDerived (Spec R)).obj K) a :=
    inferInstanceAs ((DerivedCategory.Q.obj K).IsGE a)
  have : DerivedCategory.IsLE (C := (Spec R).Modules) ((toDerived (Spec R)).obj K) b :=
    inferInstanceAs ((DerivedCategory.Q.obj K).IsLE b)
  obtain ⟨L, hge, hle, e⟩ := exists_bounded_module_representative_of_quasicoherent_homology
    R ((toDerived (Spec R)).obj K) a b (fun i =>
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctorFactors (Spec R).Modules i).app K).symm
        (locallyPerfect_quasicoherent_homology hK i))
  exact ⟨L, a, b, hge, hle, e⟩

end Quillen.PerfectComplexes.Affine
