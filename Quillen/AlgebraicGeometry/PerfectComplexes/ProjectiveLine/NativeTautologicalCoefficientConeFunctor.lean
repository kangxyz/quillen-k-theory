/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientCone
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientConeFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-!
# Actual native supported coefficient-cone functor and restriction

The literal inverse-affine restriction of the original signed coefficient cone is exact.
The existing negative-chart cone isomorphisms are natural in every perfect coefficient map.
Their actual natural isomorphism identifies the original supported restriction K-maps in every
connective degree, including zero. No self-track boundary or canonical-null comparison is asserted.
-/
@[expose] public section

open CategoryTheory.ExactCategory

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open FlasqueTwoSummands

/-- Original signed coefficient cones with the same inverse-affine restriction and support. -/
def nativeTautologicalCoefficientConeFunctor (R : CommRingCat.{u}) :
    Perfect (twoChartLine R) ⥤ (perfectSupported (positiveOpen R).ι).FullSubcategory :=
  (perfectSupported (positiveOpen R).ι).lift
    (tautologicalCoefficientConeFunctor R ⋙ (perfectSupported (plusChart R)).ι ⋙
      restrict (nativeAffineIso R).inv)
    (fun K => (nativeTautologicalCoefficientSupportedCone R K).property)

/-- Every object is the unchanged original native supported coefficient cone. -/
theorem nativeTautologicalCoefficientConeFunctor_obj (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (nativeTautologicalCoefficientConeFunctor R).obj K =
      nativeTautologicalCoefficientSupportedCone R K := rfl

/-- The actual coefficient arrow is the original cone arrow restricted by inverse affine. -/
theorem nativeTautologicalCoefficientConeFunctor_map_hom (R : CommRingCat.{u})
    {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    ((nativeTautologicalCoefficientConeFunctor R).map g).hom =
      (restrict (nativeAffineIso R).inv).map
        ((tautologicalCoefficientConeFunctor R).map g).hom := rfl

instance nativeTautologicalCoefficientConeFunctor_additive (R : CommRingCat.{u}) :
    (nativeTautologicalCoefficientConeFunctor R).Additive := by
  unfold nativeTautologicalCoefficientConeFunctor
  infer_instance

/-- Inverse-affine restriction preserves the actual inherited coefficient-cone conflations. -/
def nativeTautologicalCoefficientConeExactFunctor (R : CommRingCat.{u}) :
    CategoryTheory.ExactCategory.ExactFunctor
      (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure
          (CochainComplex (twoChartLine R).Modules ℤ)) (locallyPerfect _))
      (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
        (CategoryTheory.ExactCategory.abelianExactStructure
          (CochainComplex (nativeLineFunctor.obj (affineBase R)).obj.Modules ℤ))
        (perfectSupported (positiveOpen R).ι)) where
  toFunctor := nativeTautologicalCoefficientConeFunctor R
  map_conflation S hS := by
    change ((S.map (tautologicalCoefficientConeFunctor R ⋙
      (perfectSupported (plusChart R)).ι)).map (restrict (nativeAffineIso R).inv)).ShortExact
    exact ((tautologicalCoefficientConeExactFunctor R).map_conflation S hS).map_of_exact _

/-- The original native supported cone functor preserves all actual Waldhausen data. -/
theorem nativeTautologicalCoefficientConeFunctor_waldhausenExact (R : CommRingCat.{u}) :
    IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectSupportedWaldhausen (positiveOpen R).ι).cof
      (perfectSupportedWaldhausen (positiveOpen R).ι).weq
      (nativeTautologicalCoefficientConeFunctor R) where
  zero h := (nativeTautologicalCoefficientConeFunctor R).map_isZero h
  cofibration g hg := (nativeTautologicalCoefficientConeExactFunctor R).map_inflation g hg
  weak g hg := by
    have : QuasiIso (((tautologicalCoefficientConeFunctor R).map g).hom) :=
      (tautologicalCoefficientConeFunctor_waldhausenExact R).weak g hg
    change QuasiIso ((restrict (nativeAffineIso R).inv).map
      ((tautologicalCoefficientConeFunctor R).map g).hom)
    infer_instance
  pushout hi h := (nativeTautologicalCoefficientConeExactFunctor R).map_isPushout hi h

private theorem restrict_cone_map_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {K₁ L₁ K₂ L₂ : CochainComplex X.Modules ℤ}
    (p : K₁ ⟶ L₁) (q : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : p ≫ b = a ≫ q) :
    (restrict j).map (CochainComplex.mappingCone.map p q a b h) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso q
          (Scheme.Modules.restrictFunctor j)).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso p
        (Scheme.Modules.restrictFunctor j)).hom ≫
          CochainComplex.mappingCone.map ((restrict j).map p) ((restrict j).map q)
            ((restrict j).map a) ((restrict j).map b)
            (by simpa only [Functor.map_comp] using congrArg ((restrict j).map) h) := by
  ext n : 1
  have hf : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.fst q).1.v n (n + 1) rfl =
    (CochainComplex.mappingCone.fst p).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  have hs : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.snd q).v n n (add_zero n) =
    (CochainComplex.mappingCone.snd p).v n n (add_zero n) ≫ b.f n := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  simp only [CochainComplex.mappingCone.map] at hf hs
  simp [restrict, CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso',
    CochainComplex.mappingCone.map, Category.assoc, -Functor.map_comp,
    ← Functor.map_comp_assoc, hf, hs]

private theorem coefficient_cone_minus_naturality (R : CommRingCat.{u})
    {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    (restrict (minusChart R)).map ((tautologicalCoefficientConeFunctor R).map g).hom ≫
        (tautologicalCoefficientConeMinusIso R L).hom =
      (tautologicalCoefficientConeMinusIso R K).hom ≫
        ((perfectSupportedScalarConeFunctor (overlapOpen R).ι
          (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
          (polynomialGlobalCoordinate_overlap R)).map
            ((perfectRestrict (minusChart R)).map g)).hom := by
  rw [tautologicalCoefficientConeFunctor_map_hom]
  dsimp only [tautologicalCoefficientConeMinusIso, Iso.trans_hom]
  rw [← Category.assoc, restrict_cone_map_naturality]
  simp only [Category.assoc]
  apply (cancel_epi (CochainComplex.mappingCone.mapHomologicalComplexIso
    (tautologicalCoefficientPerfectCoordinate R K).hom
    (Scheme.Modules.restrictFunctor (minusChart R))).hom).mpr
  have hscalar :
      ((perfectSupportedScalarConeFunctor (overlapOpen R).ι
        (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
        (polynomialGlobalCoordinate_overlap R)).map
          ((perfectRestrict (minusChart R)).map g)).hom =
      CochainComplex.mappingCone.map
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
          ((restrict (minusChart R)).obj K.obj))
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
          ((restrict (minusChart R)).obj L.obj))
        ((restrict (minusChart R)).map g.hom) ((restrict (minusChart R)).map g.hom)
        ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).naturality
          ((restrict (minusChart R)).map g.hom)).symm := rfl
  rw [hscalar]
  dsimp only [CochainComplex.mappingCone.isoOfIso, restrict]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    perfectTensorByLine, ObjectProperty.lift, ObjectProperty.ι_obj, restrict, Iso.app_hom] using
    (tensorByLineComplexChartIso (minusChart R) (tautologicalLine R)
      (tautologicalLineMinusIso R)).hom.naturality g.hom

/-- The fixed old negative supported cone component is natural on every coefficient map. -/
theorem nativeTautologicalCoefficientSupportedConeMinusIso_naturality
    (R : CommRingCat.{u}) {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    (perfectSupportedRestrict (affineNativeChart R false) (positiveOpen R)).map
        ((nativeTautologicalCoefficientConeFunctor R).map g) ≫
          (nativeTautologicalCoefficientSupportedConeMinusIso R L).hom =
      (nativeTautologicalCoefficientSupportedConeMinusIso R K).hom ≫
        (perfectSupportedScalarConeFunctor (overlapOpen R).ι
          (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
          (polynomialGlobalCoordinate_overlap R)).map
            ((perfectRestrict (minusChart R)).map g) := by
  apply ObjectProperty.hom_ext
  change (restrict (affineNativeChart R false)).map
      ((restrict (nativeAffineIso R).inv).map ((tautologicalCoefficientConeFunctor R).map g).hom) ≫
        (nativeTautologicalCoefficientConeMinusIso R L).hom =
    (nativeTautologicalCoefficientConeMinusIso R K).hom ≫ _
  have hn := (restrictCompIso (affineNativeChart R false) (nativeAffineIso R).inv ≪≫
    eqToIso (restrict_congr (affineNativeChart_false_inverseAffine R))).hom.naturality
      ((tautologicalCoefficientConeFunctor R).map g).hom
  have hn' := congrArg (fun z => z ≫ (tautologicalCoefficientConeMinusIso R L).hom) hn
  simpa only [nativeTautologicalCoefficientConeMinusIso, Iso.trans_hom,
    Iso.app_hom, NatTrans.comp_app,
    Functor.comp_map, Functor.comp_obj, tautologicalCoefficientConeFunctor_obj,
    perfectRestrict, ObjectProperty.lift, ObjectProperty.ι_obj,
    Category.assoc, coefficient_cone_minus_naturality R g] using hn'

/-- The full natural isomorphism has exactly the existing original cone components. -/
def nativeTautologicalCoefficientConeMinusNatIso (R : CommRingCat.{u}) :
    nativeTautologicalCoefficientConeFunctor R ⋙
        perfectSupportedRestrict (affineNativeChart R false) (positiveOpen R) ≅
      perfectRestrict (minusChart R) ⋙
        perfectSupportedScalarConeFunctor (overlapOpen R).ι
          (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
          (polynomialGlobalCoordinate_overlap R) :=
  NatIso.ofComponents (nativeTautologicalCoefficientSupportedConeMinusIso R)
    (fun g => nativeTautologicalCoefficientSupportedConeMinusIso_naturality R g)

/-- The new natural isomorphism does not replace the old chosen component. -/
theorem nativeTautologicalCoefficientConeMinusNatIso_app (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (nativeTautologicalCoefficientConeMinusNatIso R).app K =
      nativeTautologicalCoefficientSupportedConeMinusIso R K := rfl

/-- The same-degree K-map of the actual original native supported coefficient cone. -/
def nativeTautologicalCoefficientConeKMap (R : CommRingCat.{u}) (n : ℕ) :
    PerfectK (twoChartLine R) n →* PerfectSupportedK (positiveOpen R).ι n :=
  KMap (nativeTautologicalCoefficientConeFunctor_waldhausenExact R) n

/-- Actual negative supported restriction agrees in every original connective K-degree. -/
theorem nativeTautologicalCoefficientConeKMap_restrict (R : CommRingCat.{u}) (n : ℕ) :
    (perfectSupportedKRestrict (affineNativeChart R false) (positiveOpen R) n).comp
        (nativeTautologicalCoefficientConeKMap R n) =
      (perfectSupportedScalarConeKMap (overlapOpen R).ι
        (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
        (polynomialGlobalCoordinate_overlap R) n).comp
          (perfectKRestrict (minusChart R) n) := by
  unfold perfectSupportedKRestrict nativeTautologicalCoefficientConeKMap
    perfectSupportedScalarConeKMap perfectKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeTautologicalCoefficientConeMinusNatIso R) n

/-- Degree zero recovers precisely the original native supported cone object class. -/
theorem nativeTautologicalCoefficientConeKMap_objectClass (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    nativeTautologicalCoefficientConeKMap R 0
        ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K) =
      (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoefficientSupportedCone R K) :=
  KMap_kZeroObjectClass (nativeTautologicalCoefficientConeFunctor_waldhausenExact R) K

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
