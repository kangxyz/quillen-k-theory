/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.PullbackTensorCompatibility
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.PullbackUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTwoSummands

/-! # The original native two-summand map under actual open immersion

The relative line map is the actual base change of the base open immersion.
The line comparison is the canonical composition comparison for the second
projection to the original integer projective line. Restriction of the actual
left tensor functor uses the original tensor restriction isomorphism.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme.ProjectiveLine
open Quillen.Scheme.Bass Quillen.SchemeSheaf

/-- Native base change retains the original projection to the integer line. -/
@[reassoc (attr := simp)]
theorem nativeIntegerProjection_naturality {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    (nativeLineFunctor.map f).hom ≫ nativeIntegerProjection X =
      nativeIntegerProjection U := by
  simp [nativeLineFunctor, qcBaseProductFunctor, baseProductFunctor, nativeIntegerProjection]

/-- The original cartesian projection retains the literal inverse-image open used for support. -/
theorem nativeProjection_inverseImage_open {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    (W : X.obj.Opens) :
    (nativeLineFunctor.map f).hom ⁻¹ᵁ ((nativeProjection.app X).hom ⁻¹ᵁ W) =
      (nativeProjection.app U).hom ⁻¹ᵁ (f.hom ⁻¹ᵁ W) := by
  ext y
  change (nativeProjection.app X).hom ((nativeLineFunctor.map f).hom y) ∈ W ↔
    f.hom ((nativeProjection.app U).hom y) ∈ W
  have h := congrArg (fun g : (nativeLineFunctor.obj U).obj ⟶ X.obj => g y)
    (congrArg (fun g => g.hom) (nativeProjection.naturality f))
  exact Iff.of_eq (congrArg (fun z : X.obj => z ∈ W) h)

/-- The canonical second-projection composition comparison on all original modules. -/
def nativeIntegerPullbackIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    Scheme.Modules.pullback (nativeIntegerProjection X) ⋙
        Scheme.Modules.pullback (nativeLineFunctor.map f).hom ≅
      Scheme.Modules.pullback (nativeIntegerProjection U) :=
  Scheme.Modules.pullbackComp (nativeLineFunctor.map f).hom (nativeIntegerProjection X) ≪≫
    Scheme.Modules.pullbackCongr (nativeIntegerProjection_naturality f)

/-- Pullback of the original native tautological line through its original integer projection. -/
def nativeTautologicalLinePullbackIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    (Scheme.Modules.pullback (nativeLineFunctor.map f).hom).obj
        (nativeTautologicalLine X) ≅ nativeTautologicalLine U :=
  (nativeIntegerPullbackIso f).app (tautologicalLine integerRing)

/-- The canonical line comparison is natural at the original tautological inclusion. -/
theorem nativeTautologicalLinePullbackIso_inclusion {U X : QuasiCompactSchemes.{u}}
    (f : U ⟶ X) :
    (Scheme.Modules.pullback (nativeLineFunctor.map f).hom).map
        ((Scheme.Modules.pullback (nativeIntegerProjection X)).map
          (tautologicalLineInclusion integerRing)) ≫
      (nativeIntegerPullbackIso f).hom.app _ =
    (nativeTautologicalLinePullbackIso f).hom ≫
      (Scheme.Modules.pullback (nativeIntegerProjection U)).map
        (tautologicalLineInclusion integerRing) :=
  (nativeIntegerPullbackIso f).hom.naturality (tautologicalLineInclusion integerRing)

/-- The actual ordered ambient structure coordinates retain their original pullback units. -/
theorem nativeIntegerPullbackIso_unitSquare {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    (nativeIntegerPullbackIso f).hom.app
        ((SheafOfModules.unit (twoChartLine integerRing).ringCatSheaf :
          (twoChartLine integerRing).Modules) ⨯
            SheafOfModules.unit (twoChartLine integerRing).ringCatSheaf) ≫
      (pullbackUnitSquareIso (nativeIntegerProjection U)).hom =
    (Scheme.Modules.pullback (nativeLineFunctor.map f).hom).map
        (pullbackUnitSquareIso (nativeIntegerProjection X)).hom ≫
      (pullbackUnitSquareIso (nativeLineFunctor.map f).hom).hom := by
  simp only [nativeIntegerPullbackIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [pullbackUnitSquareIso_congr, pullbackUnitSquareIso_comp]

/-- The canonical original line comparison preserves the literal ordered tautological subline. -/
theorem nativeTautologicalLinePullbackIso_originalSubline {U X : QuasiCompactSchemes.{u}}
    (f : U ⟶ X) :
    (Scheme.Modules.pullback (nativeLineFunctor.map f).hom).map
        ((Scheme.Modules.pullback (nativeIntegerProjection X)).map
            (tautologicalLineInclusion integerRing) ≫
          (pullbackUnitSquareIso (nativeIntegerProjection X)).hom) ≫
      (pullbackUnitSquareIso (nativeLineFunctor.map f).hom).hom =
    (nativeTautologicalLinePullbackIso f).hom ≫
      (Scheme.Modules.pullback (nativeIntegerProjection U)).map
        (tautologicalLineInclusion integerRing) ≫
      (pullbackUnitSquareIso (nativeIntegerProjection U)).hom := by
  rw [Functor.map_comp, Category.assoc, ← nativeIntegerPullbackIso_unitSquare,
    ← Category.assoc, nativeTautologicalLinePullbackIso_inclusion, Category.assoc]

/-- Restriction of the actual second pullback, natural in every original module. -/
def nativeIntegerPullbackOpenIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    Scheme.Modules.pullback (nativeIntegerProjection X) ⋙
        Scheme.Modules.restrictFunctor (nativeLineFunctor.map f).hom ≅
      Scheme.Modules.pullback (nativeIntegerProjection U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback (nativeIntegerProjection X))
      (Scheme.Modules.restrictFunctorIsoPullback (nativeLineFunctor.map f).hom) ≪≫
    Scheme.Modules.pullbackComp (nativeLineFunctor.map f).hom (nativeIntegerProjection X) ≪≫
    Scheme.Modules.pullbackCongr (nativeIntegerProjection_naturality f)

/-- Canonical restriction of the actual original native tautological line. -/
def nativeTautologicalLineOpenIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    (nativeTautologicalLine X).restrict (nativeLineFunctor.map f).hom ≅
      nativeTautologicalLine U :=
  (nativeIntegerPullbackOpenIso f).app (tautologicalLine integerRing)

/-- The comparison preserves the actual original integer tautological inclusion. -/
theorem nativeTautologicalLineOpenIso_inclusion {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    (Scheme.Modules.restrictFunctor (nativeLineFunctor.map f).hom).map
        ((Scheme.Modules.pullback (nativeIntegerProjection X)).map
          (tautologicalLineInclusion integerRing)) ≫
      (nativeIntegerPullbackOpenIso f).hom.app _ =
    (nativeTautologicalLineOpenIso f).hom ≫
      (Scheme.Modules.pullback (nativeIntegerProjection U)).map
        (tautologicalLineInclusion integerRing) :=
  (nativeIntegerPullbackOpenIso f).hom.naturality (tautologicalLineInclusion integerRing)

end Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine
open Quillen.Scheme Quillen.Scheme.Bass Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.Waldhausen

/-- The original chart naturality square keeps the actual original polynomial map. -/
@[reassoc (attr := simp)]
theorem nativeChart_base_naturality {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) (b : Bool) :
    nativeChart U b ≫ (nativeLineFunctor.map f).hom =
      (polynomialFunctor.map f).hom ≫ nativeChart X b := by
  cases b
  · exact (congrArg (fun g => g.hom) (nativeMinus.naturality f)).symm
  · exact (congrArg (fun g => g.hom) (nativePlus.naturality f)).symm

/-- Base change of either original native chart is the actual corresponding source chart. -/
theorem nativeChart_base_isPullback {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) (b : Bool) :
    IsPullback (nativeChart U b) (polynomialFunctor.map f).hom
      (nativeLineFunctor.map f).hom (nativeChart X b) := by
  cases b
  · apply IsPullback.flip
    apply IsPullback.of_right
      (h₁₂ := pullback.snd (toIntegerBase X.obj)
        (PolynomialLaurent.polynomialProjection integerRing))
      (h₂₂ := nativeIntegerProjection X)
    · simpa [nativeChart, polynomialFunctor, qcBaseProductFunctor, baseProductFunctor] using
        (nativeMinus_isPullback U).flip
    · exact (nativeChart_base_naturality f false).symm
    · exact (nativeMinus_isPullback X).flip
  · apply IsPullback.flip
    apply IsPullback.of_right
      (h₁₂ := pullback.snd (toIntegerBase X.obj)
        (PolynomialLaurent.polynomialProjection integerRing))
      (h₂₂ := nativeIntegerProjection X)
    · simpa [nativeChart, polynomialFunctor, qcBaseProductFunctor, baseProductFunctor] using
        (nativePlus_isPullback U).flip
    · exact (nativeChart_base_naturality f true).symm
    · exact (nativePlus_isPullback X).flip

/-- The original tensor mate is invertible by the unchanged original native line charts. -/
instance nativeOpenLinePullbackTensorMap_isIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    (E : (nativeLineFunctor.obj X).obj.Modules) :
    IsIso (modulePullbackTensorMap (nativeLineFunctor.map f).hom (nativeTautologicalLine X) E) := by
  apply modulePullbackTensorMap_isIso_of_trivializingCover (nativeLineFunctor.map f).hom
    (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X) (nativeChart_cover X)
    (nativeTautologicalLine X) E (nativeLineChartIso X)

/-- The natural comparison has exactly the original pullback-tensor mate as its forward arrow. -/
def nativeTwistPullbackModuleIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X) ⋙
        Scheme.Modules.pullback (nativeLineFunctor.map f).hom ≅
      Scheme.Modules.pullback (nativeLineFunctor.map f).hom ⋙
        moduleTensorLeftFunctor (nativeLineFunctor.obj U).obj
          ((Scheme.Modules.pullback (nativeLineFunctor.map f).hom).obj
            (nativeTautologicalLine X)) :=
  NatIso.ofComponents
    (fun E => asIso (modulePullbackTensorMap (nativeLineFunctor.map f).hom
      (nativeTautologicalLine X) E))
    (fun g => modulePullbackTensorMap_naturality_right (nativeLineFunctor.map f).hom _ g)

/-- Actual pullback tensor followed by the canonical original native line comparison. -/
def nativeTwistPullbackNativeModuleIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X) :
    moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X) ⋙
        Scheme.Modules.pullback (nativeLineFunctor.map f).hom ≅
      Scheme.Modules.pullback (nativeLineFunctor.map f).hom ⋙
        moduleTensorLeftFunctor (nativeLineFunctor.obj U).obj (nativeTautologicalLine U) :=
  nativeTwistPullbackModuleIso f ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback (nativeLineFunctor.map f).hom)
      ((SheafOfModulesOfCommRing.tensorFunctor (nativeLineFunctor.obj U).obj.sheaf).mapIso
        (nativeTautologicalLinePullbackIso f))

/-- Open restriction uses the original tensor mate and canonical restriction/pullback map. -/
def nativeTwistOpenModuleIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X) ⋙
        Scheme.Modules.restrictFunctor (nativeLineFunctor.map f).hom ≅
      Scheme.Modules.restrictFunctor (nativeLineFunctor.map f).hom ⋙
        moduleTensorLeftFunctor (nativeLineFunctor.obj U).obj (nativeTautologicalLine U) :=
  Functor.isoWhiskerLeft
      (moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X))
      (Scheme.Modules.restrictFunctorIsoPullback (nativeLineFunctor.map f).hom) ≪≫
    nativeTwistPullbackNativeModuleIso f ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback (nativeLineFunctor.map f).hom).symm
      (moduleTensorLeftFunctor (nativeLineFunctor.obj U).obj (nativeTautologicalLine U))

/-- Degreewise actual tensor and actual restriction retain their module comparison. -/
def nativeTwistOpenComplexIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    tensorByLineComplex (nativeTautologicalLine X) ⋙ restrict (nativeLineFunctor.map f).hom ≅
      restrict (nativeLineFunctor.map f).hom ⋙ tensorByLineComplex (nativeTautologicalLine U) :=
  Functor.mapHomologicalComplexCompIso (nativeTwistOpenModuleIso f) (.up ℤ)

/-- The actual exact negative twist commutes with actual open restriction. -/
def nativeNegativeTwistOpenIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    nativeNegativeTwist X ⋙ perfectRestrict (nativeLineFunctor.map f).hom ≅
      perfectRestrict (nativeLineFunctor.map f).hom ⋙ nativeNegativeTwist U :=
  Functor.fullyFaithfulCancelRight (locallyPerfect (nativeLineFunctor.obj U).obj).ι
    (Functor.isoWhiskerLeft (locallyPerfect (nativeLineFunctor.obj X).obj).ι
      (nativeTwistOpenComplexIso f))

/-- The structure-line summand uses the canonical pullback composition comparison. -/
def nativeFirstSummandOpenIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    nativeFirstSummand X ⋙ perfectRestrict (nativeLineFunctor.map f).hom ≅
      perfectRestrict f.hom ⋙ nativeFirstSummand U :=
  Functor.isoWhiskerLeft (nativeFirstSummand X)
      (perfectRestrictIsoFlatPullback (nativeLineFunctor.map f).hom) ≪≫
    (perfectFlatPullbackCompIso (nativeLineFunctor.map f).hom
      (nativeProjection.app X).hom).symm ≪≫
    eqToIso (by congr 1; exact congrArg (fun g => g.hom) (nativeProjection.naturality f)) ≪≫
    perfectFlatPullbackCompIso (nativeProjection.app U).hom f.hom ≪≫
    Functor.isoWhiskerRight (perfectRestrictIsoFlatPullback f.hom).symm (nativeFirstSummand U)

/-- The second summand retains original left tensor and canonical pullback. -/
def nativeSecondSummandOpenIso {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] :
    nativeSecondSummand X ⋙ perfectRestrict (nativeLineFunctor.map f).hom ≅
      perfectRestrict f.hom ⋙ nativeSecondSummand U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (nativeFirstSummand X) (nativeNegativeTwistOpenIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (nativeFirstSummandOpenIso f) (nativeNegativeTwist U) ≪≫
    Functor.associator _ _ _

/-- The first-summand equation uses unchanged K-groups, including degree zero. -/
theorem nativeFirstSummandKMap_open {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] (n : ℕ) :
    (perfectKRestrict (nativeLineFunctor.map f).hom n).comp
        (KMap (nativeFirstSummand_exact X) n) =
      (KMap (nativeFirstSummand_exact U) n).comp (perfectKRestrict f.hom n) := by
  rw [perfectKRestrict, perfectKRestrict, KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeFirstSummandOpenIso f) n

/-- Canonical original negative-summand naturality in every original nonnegative degree. -/
theorem nativeSecondSummandKMap_open {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] (n : ℕ) :
    (perfectKRestrict (nativeLineFunctor.map f).hom n).comp
        (KMap (nativeSecondSummand_exact X) n) =
      (KMap (nativeSecondSummand_exact U) n).comp (perfectKRestrict f.hom n) := by
  rw [perfectKRestrict, perfectKRestrict, KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeSecondSummandOpenIso f) n

/-- The unchanged original native two-summand map is natural under actual base open immersion. -/
theorem nativeTwoSummandKMap_open {U X : QuasiCompactSchemes.{u}} (f : U ⟶ X)
    [IsOpenImmersion f.hom] (n : ℕ) (a b : PerfectK X.obj n) :
    perfectKRestrict (nativeLineFunctor.map f).hom n (nativeTwoSummandKMap X n (a, b)) =
      nativeTwoSummandKMap U n (perfectKRestrict f.hom n a, perfectKRestrict f.hom n b) := by
  rw [nativeTwoSummandKMap_apply, map_mul, nativeTwoSummandKMap_apply]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (nativeFirstSummandKMap_open f n) a)
    (DFunLike.congr_fun (nativeSecondSummandKMap_open f n) b)

end Quillen.PerfectComplexes.ProjectiveLine
