/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.TwoOpen
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.BoundedComparison
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Canonical native projection base change on arbitrary perfect objects

The original derived flat-base-change mate for the native projective line is
invertible on every intrinsic perfect object. The input need not have globally
finite locally free terms: bounded quasicoherent cohomology and the original
two-chart calculation on single sheaves suffice. This is a projection
prerequisite; it does not assert that the direct image is perfect, nor a
projective-line K-equivalence.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.ProjectiveLine


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The standard derived category of module sheaves, used for native projection base change. -/
local instance nativePerfectProjectionStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

private theorem isIso_on_perfect_of_quasicoherent_single
    {U V : Scheme.{u}} [CompactSpace U]
    {F G : DerivedCategory.Plus U.Modules ⥤ DerivedCategory.Plus V.Modules}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [τ.CommShift ℤ]
    (hsingle : ∀ (M : U.Modules), M.IsQuasicoherent →
      IsIso (τ.app ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)))
    (K : DerivedCategory.Plus U.Modules)
    (hK : perfectDerivedObjects U (DerivedCategory.Plus.ι.obj K)) :
    IsIso (τ.app K) := by
  let P : ObjectProperty (DerivedCategory.Plus U.Modules) := fun A => IsIso (τ.app A)
  let : P.IsClosedUnderIsomorphisms := ⟨by
    intro A B e hA
    have : IsIso (τ.app A) := hA
    change IsIso (τ.app B)
    have h : τ.app B = F.map e.inv ≫ τ.app A ≫ G.map e.hom := by
      rw [← τ.naturality, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]
    rw [h]
    infer_instance⟩
  let : P.IsTriangulated := {
    isStableUnderShiftBy n := ⟨by
      intro A hA
      have : IsIso (τ.app A) := hA
      change IsIso (τ.app (A⟦n⟧))
      rw [τ.app_shift]
      infer_instance⟩
    exists_zero := ⟨0, isZero_zero _,
      (F.map_isZero (isZero_zero _)).isIso (G.map_isZero (isZero_zero _)) (τ.app 0)⟩
    toIsTriangulatedClosed₂ := .mk' (by
      intro T hT h₁ h₃
      exact τ.isIso_app_middle_of_distinguished T hT h₁ h₃) }
  let Q := P.map DerivedCategory.Plus.ι
  have hsing (M : U.Modules) (hM : M.IsQuasicoherent) (n : ℤ) :
      Q ((DerivedCategory.singleFunctor U.Modules n).obj M) := by
    have h₀ : P ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) := hsingle M hM
    have hn : P ((DerivedCategory.Plus.singleFunctor U.Modules n).obj M) :=
      P.prop_of_iso (((DerivedCategory.Plus.singleFunctors U.Modules).shiftIso
        (-n) n 0 (by omega)).app M) (P.le_shift (-n) _ h₀)
    exact ⟨_, hn, ⟨(DerivedCategory.Plus.singleFunctorιIso U.Modules n).app M⟩⟩
  obtain ⟨L, ⟨eL⟩⟩ := (perfectDerivedObjects_iff_exists_representative U _).mp hK
  obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded L.property
  have : L.obj.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hab i (Or.inl hi)
  have : L.obj.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hab i (Or.inr hi)
  have : DerivedCategory.IsGE (C := U.Modules) ((DerivedCategory.Q (C := U.Modules)).obj L.obj) a :=
    inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsGE a)
  have : DerivedCategory.IsLE (C := U.Modules) ((DerivedCategory.Q (C := U.Modules)).obj L.obj) b :=
    inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsLE b)
  have : (DerivedCategory.Plus.ι.obj K).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eL a
  have : (DerivedCategory.Plus.ι.obj K).IsLE b :=
    DerivedCategory.TStructure.t.isLE_of_iso eL b
  have hq (i : ℤ) :
      ((DerivedCategory.homologyFunctor U.Modules i).obj
        (DerivedCategory.Plus.ι.obj K)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors U.Modules i).app L.obj).symm ≪≫
        (DerivedCategory.homologyFunctor U.Modules i).mapIso eL)
      (locallyPerfect_quasicoherent_homology L.property i)
  let QC : ObjectProperty U.Modules := SheafOfModules.isQuasicoherent U.ringCatSheaf
  let : QC.IsClosedUnderIsomorphisms :=
    inferInstanceAs (SheafOfModules.isQuasicoherent U.ringCatSheaf).IsClosedUnderIsomorphisms
  have hQ : Q (DerivedCategory.Plus.ι.obj K) :=
    Quillen.DerivedHomComparison.property_of_bounded_homology_single_generation
      (C := U.Modules) Q QC (by change (0 : U.Modules).IsQuasicoherent; infer_instance)
      hsing _ a b hq
  obtain ⟨A, hA, ⟨eA⟩⟩ := hQ
  exact P.prop_of_iso (DerivedCategory.Plus.ι.preimageIso eA) hA

/-- The actual native two-chart projection mate is invertible on every quasicoherent single. -/
theorem isIso_nativeProjectionBaseChange_single
    {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) [Flat f.hom]
    (M : (nativeLineFunctor.obj Y).obj.Modules) [M.IsQuasicoherent] :
    IsIso ((derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
      (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom
      (nativeMap_isPullback f)).app
        ((DerivedCategory.Plus.singleFunctor (nativeLineFunctor.obj Y).obj.Modules 0).obj M)) := by
  let : IsAffineHom (PolynomialLaurent.Relative.plus.app Y).hom :=
    MorphismProperty.of_isPullback
      (baseProductTransformation_isPullback _ _ _
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentPlus_projection integerRing) Y.obj).flip
      inferInstance
  let : IsAffineHom (PolynomialLaurent.Relative.polynomialProjection.app Y).hom := by
    change IsAffineHom (pullback.fst (toIntegerBase Y.obj)
      (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection integerRing))
    exact MorphismProperty.pullback_fst _ _
      (inferInstance : IsAffineHom
        (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection integerRing))
  let : IsAffineHom ((nativePlus.app Y).hom ≫ (nativeProjection.app Y).hom) := by
    simpa only [← ObjectProperty.FullSubcategory.comp_hom, nativePlus_projection] using
      (inferInstance : IsAffineHom (PolynomialLaurent.Relative.polynomialProjection.app Y).hom)
  let : IsAffineHom ((nativeMinus.app Y).hom ≫ (nativeProjection.app Y).hom) := by
    simpa only [← ObjectProperty.FullSubcategory.comp_hom, nativeMinus_projection] using
      (inferInstance : IsAffineHom (PolynomialLaurent.Relative.polynomialProjection.app Y).hom)
  let : IsAffineHom (((PolynomialLaurent.Relative.plus.app Y).hom ≫ (nativePlus.app Y).hom) ≫
      (nativeProjection.app Y).hom) := by
    rw [Category.assoc]
    infer_instance
  exact isIso_derivedFlatBaseChangeMap_twoOpen_single _ _ _ _ (nativeMap_isPullback f)
    (PolynomialLaurent.Relative.plus.app Y).hom (PolynomialLaurent.Relative.minus.app Y).hom
    (nativePlus.app Y).hom (nativeMinus.app Y).hom
    (native_chart_isPullback Y) (native_charts_cover Y) M

/-- Canonical flat base change for the original native projection on arbitrary intrinsic
perfect objects. No global strict model, finite term window, or generation premise is assumed. -/
theorem isIso_nativeProjectionBaseChange_perfect
    {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) [Flat f.hom]
    (K : DerivedCategory.Plus (nativeLineFunctor.obj Y).obj.Modules)
    (hK : perfectDerivedObjects (nativeLineFunctor.obj Y).obj
      (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
      (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom
      (nativeMap_isPullback f)).app K) := by
  let := flat_cartesian_baseChange (nativeLineFunctor.map f).hom
    (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom (nativeMap_isPullback f)
  let := derivedFlatBaseChangeMap_commShift (nativeLineFunctor.map f).hom
    (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom (nativeMap_isPullback f)
  let : (derivedPushforwardPlus (nativeProjection.app Y).hom ⋙
      derivedFlatPullbackPlus f.hom).IsTriangulated := by
    dsimp [derivedPushforwardPlus, derivedFlatPullbackPlus]
    infer_instance
  let : (derivedFlatPullbackPlus (nativeLineFunctor.map f).hom ⋙
      derivedPushforwardPlus (nativeProjection.app X).hom).IsTriangulated := by
    dsimp [derivedPushforwardPlus, derivedFlatPullbackPlus]
    infer_instance
  let : (derivedPushforwardPlus (nativeProjection.app Y).hom ⋙
      derivedFlatPullbackPlus f.hom).Additive := by
    dsimp [derivedPushforwardPlus, derivedFlatPullbackPlus]
    infer_instance
  let : (derivedFlatPullbackPlus (nativeLineFunctor.map f).hom ⋙
      derivedPushforwardPlus (nativeProjection.app X).hom).Additive := by
    dsimp [derivedPushforwardPlus, derivedFlatPullbackPlus]
    infer_instance
  apply isIso_on_perfect_of_quasicoherent_single _ _ K hK
  intro M hM
  exact isIso_nativeProjectionBaseChange_single f M

/-- The original locally perfect complexes on the native line, placed in the actual bounded-below
derived category using their proved cohomological bounds. The original complex is retained. -/
def nativePerfectToDerivedPlus (X : QuasiCompactSchemes.{u}) :
    Perfect (nativeLineFunctor.obj X).obj ⥤
      DerivedCategory.Plus (nativeLineFunctor.obj X).obj.Modules :=
  DerivedCategory.TStructure.t.plus.lift
    ((locallyPerfect (nativeLineFunctor.obj X).obj).ι ⋙
      DerivedCategory.Q (C := (nativeLineFunctor.obj X).obj.Modules)) (fun K => by
    obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded K.property
    have : K.obj.IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hab i (Or.inl hi)
    exact ⟨a, inferInstanceAs ((DerivedCategory.Q.obj K.obj).IsGE a)⟩)

/-- Forgetting the lower-bound proof gives the literal original perfect-complex localization. -/
def nativePerfectToDerivedPlusFactors (X : QuasiCompactSchemes.{u}) :
    nativePerfectToDerivedPlus X ⋙ DerivedCategory.Plus.ι ≅
      (locallyPerfect (nativeLineFunctor.obj X).obj).ι ⋙
        DerivedCategory.Q (C := (nativeLineFunctor.obj X).obj.Modules) := Iso.refl _

/-- The canonical native projection base-change isomorphism on the original category of all
locally perfect complexes. Its forward map is the installed derived flat-base-change mate. -/
def nativePerfectProjectionBaseChangeIso
    {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) [Flat f.hom] :
    letI := flat_cartesian_baseChange (nativeLineFunctor.map f).hom
      (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom (nativeMap_isPullback f)
    nativePerfectToDerivedPlus Y ⋙
        (derivedPushforwardPlus (nativeProjection.app Y).hom ⋙ derivedFlatPullbackPlus f.hom) ≅
      nativePerfectToDerivedPlus Y ⋙
        (derivedFlatPullbackPlus (nativeLineFunctor.map f).hom ⋙
          derivedPushforwardPlus (nativeProjection.app X).hom) := by
  let := flat_cartesian_baseChange (nativeLineFunctor.map f).hom
    (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom (nativeMap_isPullback f)
  let τ := Functor.whiskerLeft (nativePerfectToDerivedPlus Y)
    (derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
      (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom (nativeMap_isPullback f))
  have hτ (K : Perfect (nativeLineFunctor.obj Y).obj) : IsIso (τ.app K) :=
    isIso_nativeProjectionBaseChange_perfect f ((nativePerfectToDerivedPlus Y).obj K)
      ((perfectDerivedObjects_toDerived_iff _ K.obj).mpr K.property)
  exact NatIso.ofComponents (fun K => asIso (τ.app K)) (fun g => τ.naturality g)

/-- The natural comparison retains the original canonical mate on every original perfect input. -/
theorem nativePerfectProjectionBaseChangeIso_hom_app
    {X Y : QuasiCompactSchemes.{u}} (f : X ⟶ Y) [Flat f.hom]
    (K : Perfect (nativeLineFunctor.obj Y).obj) :
    (nativePerfectProjectionBaseChangeIso f).hom.app K =
      (derivedFlatBaseChangeMap (nativeLineFunctor.map f).hom
        (nativeProjection.app X).hom (nativeProjection.app Y).hom f.hom
        (nativeMap_isPullback f)).app ((nativePerfectToDerivedPlus Y).obj K) := rfl

end Quillen.PerfectComplexes.ProjectiveLine
