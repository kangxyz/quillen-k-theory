/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPerfect
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.Strictification

/-!
# The original affine perfect derived equivalence

The original associated-sheaf derived functor restricts to a triangulated
equivalence between actual derived module objects represented by bounded
finite-projective complexes and intrinsic perfect objects in the original
ambient sheaf derived category. Both fullness and essential surjectivity
are proved using bounded derived comparison and affine strictification.

The forward morphisms are literally the original `associatedDerived` maps.
Every integer cohomological upper and lower bound is preserved and reflected.
For any derived module object, perfectness is detected by its original
associated derived sheaf object; no bounds are supplied to this criterion.
The natural principal comparison retains original scalar localization,
`derivedRestrict`, and the canonical principal comparison isomorphism.

All rings are arbitrary. This is a statement about actual perfect derived
subcategories, not an unbounded QC equivalence or a Waldhausen enhancement
comparison.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped ZeroObject
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).ContainsZero where
  exists_zero := by
    let := ModuleCat.isZero_iff_subsingleton.mp (show IsZero (0 : ModuleCat.{u} R) from isZero_zero
      _)
    let P := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (0 : ModuleCat.{u} R)
    exact ⟨DerivedCategory.Q.obj P, DerivedCategory.Q.map_isZero
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).map_isZero (isZero_zero _)),
      ⟨P, moduleStrictPerfect_single R 0 _, ⟨Iso.refl _⟩⟩⟩

instance (R : CommRingCat.{u}) : (finiteProjectiveDerivedObjects R).IsTriangulated where

/-- A genuine bounded finite-projective representative supplies finite cohomological bounds. -/
lemma finiteProjectiveDerived_bounded (R : CommRingCat.{u})
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : finiteProjectiveDerivedObjects R K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨P, ⟨⟨a, b, hb⟩, _⟩, ⟨e⟩⟩ := hK
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).mpr (fun i hi => hb i (Or.inl
    hi))
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).mpr (fun i hi => hb i (Or.inr
    hi))
  exact ⟨a, b, DerivedCategory.TStructure.t.isGE_of_iso e a,
    DerivedCategory.TStructure.t.isLE_of_iso e b⟩

/-- The actual full triangulated subcategory of finite-projective derived module objects. -/
abbrev PerfectModuleDerived (R : CommRingCat.{u}) := (finiteProjectiveDerivedObjects
  R).FullSubcategory

/-- The literal original affine derived functor on actual perfect module objects. -/
def associatedPerfectDerived (R : CommRingCat.{u}) : PerfectModuleDerived R ⥤ Derived (Spec R) :=
  (finiteProjectiveDerivedObjects R).ι ⋙ associatedDerived R

instance (R : CommRingCat.{u}) : (associatedPerfectDerived R).CommShift ℤ := by
  dsimp only [associatedPerfectDerived]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedPerfectDerived R).IsTriangulated := by
  dsimp only [associatedPerfectDerived]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedPerfectDerived R).Full where
  map_surjective {X Y} f := by
    obtain ⟨a, b, hga, hlb⟩ := finiteProjectiveDerived_bounded R X.property
    obtain ⟨c, d, hgc, hld⟩ := finiteProjectiveDerived_bounded R Y.property
    obtain ⟨g, hg⟩ := (associatedDerived_bounded_map_bijective R X.obj Y.obj a b c d).surjective f
    exact ⟨ObjectProperty.homMk g, hg⟩

instance (R : CommRingCat.{u}) : (associatedPerfectDerived R).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨a, b, hga, hlb⟩ := finiteProjectiveDerived_bounded R X.property
    obtain ⟨c, d, hgc, hld⟩ := finiteProjectiveDerived_bounded R Y.property
    apply ObjectProperty.hom_ext
    exact (associatedDerived_bounded_map_bijective R X.obj Y.obj a b c d).injective h

/-- The original affine comparison has exactly the intrinsic perfect sheaf objects as its perfect
  essential image. -/
lemma associatedPerfectDerived_essImage_iff (R : CommRingCat.{u}) (K : Derived (Spec R)) :
    (associatedPerfectDerived R).essImage K ↔ perfectDerivedObjects (Spec R) K := by
  constructor
  · rintro ⟨A, ⟨eA⟩⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := A.property
    apply (perfectDerivedObjects_iff_exists_representative (Spec R) K).mpr
    exact ⟨⟨(associatedComplex R).obj P, locallyPerfect_of_strictPerfect (strictPerfect_associated R
      hP)⟩,
      ⟨((associatedDerivedFactors R).app P).symm ≪≫ (associatedDerived R).mapIso eP ≪≫ eA⟩⟩
  · intro hK
    obtain ⟨L, ⟨eL⟩⟩ := (perfectDerivedObjects_iff_exists_representative (Spec R) K).mp hK
    obtain ⟨P, hP, ⟨eP⟩⟩ := locallyPerfect_exists_moduleStrictPerfect_representative R L.property
    exact ⟨⟨DerivedCategory.Q.obj P, ⟨P, hP, ⟨Iso.refl _⟩⟩⟩,
      ⟨(associatedDerivedFactors R).app P ≪≫ eP ≪≫ eL⟩⟩

/-- Original affine associated sheaves detect perfectness of every derived
module object; boundedness is proved from local perfection, not supplied. -/
lemma finiteProjectiveDerived_iff_associated_perfect (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R)) :
    finiteProjectiveDerivedObjects R K ↔
      perfectDerivedObjects (Spec R) ((associatedDerived R).obj K) := by
  constructor
  · intro hK
    exact (associatedPerfectDerived_essImage_iff R _).mp ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩
  · intro hK
    obtain ⟨A, ⟨e⟩⟩ := (associatedPerfectDerived_essImage_iff R _).mpr hK
    obtain ⟨a, b, hga, hlb⟩ := finiteProjectiveDerived_bounded R A.property
    let e' : (associatedDerived R).obj A.obj ≅ (associatedDerived R).obj K := e
    have hge : DerivedCategory.IsGE (C := (Spec R).Modules)
        ((associatedDerived R).obj K) a :=
      (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isGE_of_iso e' a
    have hle : DerivedCategory.IsLE (C := (Spec R).Modules)
        ((associatedDerived R).obj K) b :=
      (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isLE_of_iso e' b
    have : K.IsGE a := (DerivedHomComparison.mapDerivedCategory_isGE_iff (tilde.functor R) K a).mp
      hge
    have : K.IsLE b := (DerivedHomComparison.mapDerivedCategory_isLE_iff (tilde.functor R) K b).mp
      hle
    exact (finiteProjectiveDerivedObjects R).prop_of_iso
      (associatedDerivedIsoLiftBounded R A.obj K a b a b e) A.property

/-- Equality of actual essential-image and intrinsic perfectness predicates. -/
lemma associatedPerfectDerived_essImage_eq (R : CommRingCat.{u}) :
    (associatedPerfectDerived R).essImage = perfectDerivedObjects (Spec R) := by
  funext K
  exact propext (associatedPerfectDerived_essImage_iff R K)

/-- The original affine comparison restricted to the proved perfect source and target. -/
def associatedPerfect (R : CommRingCat.{u}) : PerfectModuleDerived R ⥤ PerfectDerived (Spec R) :=
  (perfectDerivedObjects (Spec R)).lift (associatedPerfectDerived R)
    (fun A => (associatedPerfectDerived_essImage_iff R _).mp ⟨A, ⟨Iso.refl _⟩⟩)

instance (R : CommRingCat.{u}) : (associatedPerfect R).CommShift ℤ := by
  dsimp only [associatedPerfect]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedPerfect R).IsTriangulated := by
  dsimp only [associatedPerfect]
  infer_instance

instance (R : CommRingCat.{u}) : (associatedPerfect R).Full :=
  inferInstanceAs ((perfectDerivedObjects (Spec R)).lift (associatedPerfectDerived R) _).Full

instance (R : CommRingCat.{u}) : (associatedPerfect R).Faithful :=
  inferInstanceAs ((perfectDerivedObjects (Spec R)).lift (associatedPerfectDerived R) _).Faithful

instance (R : CommRingCat.{u}) : (associatedPerfect R).EssSurj where
  mem_essImage K := by
    obtain ⟨A, ⟨e⟩⟩ := (associatedPerfectDerived_essImage_iff R K.obj).mpr K.property
    exact ⟨A, ⟨ObjectProperty.isoMk (perfectDerivedObjects (Spec R)) e⟩⟩

instance (R : CommRingCat.{u}) : (associatedPerfect R).IsEquivalence where

/-- The genuine perfect derived equivalence over any commutative ring. -/
def perfectDerivedEquivalence (R : CommRingCat.{u}) :
    PerfectModuleDerived R ≌ PerfectDerived (Spec R) := (associatedPerfect R).asEquivalence

/-- The forward equivalence acts by the literal original associated-derived morphism map. -/
@[simp]
lemma perfectDerivedEquivalence_functor_map (R : CommRingCat.{u})
    {K L : PerfectModuleDerived R} (f : K ⟶ L) :
    ((perfectDerivedEquivalence R).functor.map f).hom = (associatedDerived R).map f.hom := rfl

/-- Forgetting perfectness recovers the original affine derived functor definitionally. -/
def perfectDerivedEquivalenceFactors (R : CommRingCat.{u}) :
    (perfectDerivedEquivalence R).functor ⋙ (perfectDerivedObjects (Spec R)).ι ≅
      (finiteProjectiveDerivedObjects R).ι ⋙ associatedDerived R := Iso.refl _

/-- The equivalence preserves and reflects each exact lower cohomological bound. -/
lemma perfectDerivedEquivalence_isGE_iff (R : CommRingCat.{u})
    (K : PerfectModuleDerived R) (n : ℤ) :
    DerivedCategory.IsGE (C := (Spec R).Modules)
      (((perfectDerivedEquivalence R).functor.obj K).obj) n ↔ K.obj.IsGE n :=
  DerivedHomComparison.mapDerivedCategory_isGE_iff (tilde.functor R) K.obj n

/-- The equivalence preserves and reflects each exact upper cohomological bound. -/
lemma perfectDerivedEquivalence_isLE_iff (R : CommRingCat.{u})
    (K : PerfectModuleDerived R) (n : ℤ) :
    DerivedCategory.IsLE (C := (Spec R).Modules)
      (((perfectDerivedEquivalence R).functor.obj K).obj) n ↔ K.obj.IsLE n :=
  DerivedHomComparison.mapDerivedCategory_isLE_iff (tilde.functor R) K.obj n

/-- Original scalar localization preserves actual finite-projective derived module objects. -/
lemma finiteProjectiveDerived_principalLocalization (R : CommRingCat.{u}) (r : R)
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : finiteProjectiveDerivedObjects R K) :
    finiteProjectiveDerivedObjects (CommRingCat.of (Localization.Away r))
      ((principalDerivedLocalization R r).obj K) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hK
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  exact ⟨(Quillen.ModuleComplex.PrincipalLocalization.localize r (.up ℤ)).obj P,
    moduleStrictPerfect_localize R r hP,
    ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ (principalDerivedLocalization R r).mapIso eP⟩⟩

/-- Actual principal scalar localization corestricted to perfect module objects. -/
def principalPerfectModuleLocalization (R : CommRingCat.{u}) (r : R) :
    PerfectModuleDerived R ⥤ PerfectModuleDerived (CommRingCat.of (Localization.Away r)) :=
  (finiteProjectiveDerivedObjects (CommRingCat.of (Localization.Away r))).lift
    ((finiteProjectiveDerivedObjects R).ι ⋙ principalDerivedLocalization R r)
    (fun K => finiteProjectiveDerived_principalLocalization R r K.property)

/-- The corestricted morphism is the original principal derived localization map. -/
@[simp]
lemma principalPerfectModuleLocalization_map (R : CommRingCat.{u}) (r : R)
    {K L : PerfectModuleDerived R} (f : K ⟶ L) :
    ((principalPerfectModuleLocalization R r).map f).hom =
      (principalDerivedLocalization R r).map f.hom := rfl

/-- The actual perfect derived equivalence commutes naturally with original
principal geometric restriction and original scalar localization. -/
def perfectDerivedEquivalencePrincipalIso (R : CommRingCat.{u}) (r : R) :
    principalPerfectModuleLocalization R r ⋙
      (perfectDerivedEquivalence (CommRingCat.of (Localization.Away r))).functor ≅
    (perfectDerivedEquivalence R).functor ⋙
      perfectDerivedRestrict (CoherentScheme.principalOpen R r) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((principalDerivedComparisonIso R r).app
    K.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (principalDerivedComparisonIso R r).hom.naturality f.hom)

/-- The natural perfect comparison is the specified original principal derived comparison. -/
@[simp]
lemma perfectDerivedEquivalencePrincipalIso_hom_app (R : CommRingCat.{u}) (r : R)
    (K : PerfectModuleDerived R) :
    ((perfectDerivedEquivalencePrincipalIso R r).hom.app K).hom =
      (principalDerivedComparisonIso R r).hom.app K.obj := rfl

end Quillen.PerfectComplexes.Affine
