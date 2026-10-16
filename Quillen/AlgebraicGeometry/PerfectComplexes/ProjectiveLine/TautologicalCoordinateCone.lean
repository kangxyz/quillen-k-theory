/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalFirstCoordinate
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Quillen.Algebra.Homology.MappingConeIso

/-!
# The supported cone of the original first tautological coordinate

The actual first-coordinate arrow on the two-chart line gives an arrow of degree-zero perfect
complexes. Its positive restriction is an isomorphism, so its literal signed mapping cone is
supported away from that chart. Its negative restriction is explicitly isomorphic to the cone
of the original polynomial scalar on the structure single. All chart and single/restriction
comparisons remain the original ones; no native Phi or terminal boundary calculation is asserted.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Modules

/-- The original tautological line as its degree-zero perfect single. -/
def tautologicalPerfect (R : CommRingCat.{u}) : Perfect (twoChartLine R) :=
  ⟨(CochainComplex.singleFunctor (twoChartLine R).Modules 0).obj (tautologicalLine R),
    locallyPerfect_of_strictPerfect (single_strictPerfect_int _ 0)⟩

/-- The literal first-coordinate arrow on the original degree-zero perfect singles. -/
def tautologicalCoordinatePerfect (R : CommRingCat.{u}) :
    tautologicalPerfect R ⟶ rankOnePerfect (twoChartLine R) :=
  (locallyPerfect (twoChartLine R)).homMk
    ((CochainComplex.singleFunctor (twoChartLine R).Modules 0).map
      (tautologicalInclusionFirstProjection R))

/-- The positive trivialization retains the original single/restriction comparison. -/
def tautologicalPerfectPlusIso (R : CommRingCat.{u}) :
    (restrict (plusChart R)).obj (tautologicalPerfect R).obj ≅
      (rankOnePerfect (Spec (.of (Polynomial R)))).obj :=
  (HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor (plusChart R)) (.up ℤ) 0).app (tautologicalLine R) ≪≫
    (CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).mapIso
      (tautologicalLinePlusIso R)

/-- The negative trivialization retains the original single/restriction comparison. -/
def tautologicalPerfectMinusIso (R : CommRingCat.{u}) :
    (restrict (minusChart R)).obj (tautologicalPerfect R).obj ≅
      (rankOnePerfect (Spec (.of (Polynomial R)))).obj :=
  (HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor (minusChart R)) (.up ℤ) 0).app (tautologicalLine R) ≪≫
    (CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).mapIso
      (tautologicalLineMinusIso R)

private theorem single_restriction_square {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    {M' N' : U.Modules} (a : M.restrict j ≅ M') (b : N.restrict j ≅ N')
    (g : M' ⟶ N') (h : (Scheme.Modules.restrictFunctor j).map f ≫ b.hom = a.hom ≫ g) :
    (restrict j).map ((CochainComplex.singleFunctor X.Modules 0).map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app N ≪≫
            (CochainComplex.singleFunctor U.Modules 0).mapIso b).hom =
      ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app M ≪≫
            (CochainComplex.singleFunctor U.Modules 0).mapIso a).hom ≫
        (CochainComplex.singleFunctor U.Modules 0).map g := by
  let e := HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor j) (.up ℤ) 0
  have hn := e.hom.naturality f
  change (restrict j).map ((CochainComplex.singleFunctor X.Modules 0).map f) ≫
      (e.app N).hom = (e.app M).hom ≫
        (CochainComplex.singleFunctor U.Modules 0).map
          ((Scheme.Modules.restrictFunctor j).map f) at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  simp only [e, Category.assoc]

/-- The original positive restricted arrow is the displayed trivialization square. -/
theorem tautologicalCoordinatePerfect_plus (R : CommRingCat.{u}) :
    (restrict (plusChart R)).map (tautologicalCoordinatePerfect R).hom ≫
        ((locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (plusChart R))).hom =
      (tautologicalPerfectPlusIso R).hom := by
  refine (single_restriction_square (plusChart R) (tautologicalInclusionFirstProjection R)
    (tautologicalLinePlusIso R) (Scheme.Modules.restrictUnitIso (plusChart R)) (𝟙 _)
    (by rw [tautologicalInclusionFirstProjection_plus]; simp)).trans ?_
  exact (congrArg ((tautologicalPerfectPlusIso R).hom ≫ ·)
    ((CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map_id _)).trans
      (Category.comp_id _)

/-- The original negative restriction is the actual polynomial scalar through the chart isos. -/
theorem tautologicalCoordinatePerfect_minus (R : CommRingCat.{u}) :
    (restrict (minusChart R)).map (tautologicalCoordinatePerfect R).hom ≫
        ((locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (minusChart R))).hom =
      (tautologicalPerfectMinusIso R).hom ≫
        (CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map
          (unitMul _ (polynomialCoordinate R)) := by
  exact single_restriction_square (minusChart R) (tautologicalInclusionFirstProjection R)
    (tautologicalLineMinusIso R) (Scheme.Modules.restrictUnitIso (minusChart R))
    (unitMul _ (polynomialCoordinate R))
    (by rw [tautologicalInclusionFirstProjection_minus]; simp)

/-- The positive restricted perfect arrow is genuinely invertible. -/
instance tautologicalCoordinatePerfect_plus_isIso (R : CommRingCat.{u}) :
    IsIso ((restrict (plusChart R)).map (tautologicalCoordinatePerfect R).hom) := by
  let e := (locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (plusChart R))
  have h : (restrict (plusChart R)).map (tautologicalCoordinatePerfect R).hom =
      (tautologicalPerfectPlusIso R).hom ≫ e.inv := by
    exact e.eq_comp_inv.mpr (tautologicalCoordinatePerfect_plus R)
  rw [h]
  infer_instance

/-- The original first coordinate is weak for the actual positive open localization. -/
theorem tautologicalCoordinatePerfect_openWeak (R : CommRingCat.{u}) :
    (perfectOpenWeakWaldhausen (plusChart R)).weq (tautologicalCoordinatePerfect R) := by
  rw [perfectOpenWeakWaldhausen_weq_iff]
  infer_instance

/-- The actual signed cone, supported away from the positive chart. -/
def tautologicalCoordinateSupportedCone (R : CommRingCat.{u}) :
    (perfectSupported (plusChart R)).FullSubcategory :=
  ⟨CochainComplex.mappingCone (tautologicalCoordinatePerfect R).hom,
    perfectOpenWeak_mappingCone_supported (plusChart R) (tautologicalCoordinatePerfect R)
      (tautologicalCoordinatePerfect_openWeak R)⟩

/-- The negative restriction is the original polynomial scalar cone through actual cone maps. -/
def tautologicalCoordinateConeMinusIso (R : CommRingCat.{u}) :
    (restrict (minusChart R)).obj (tautologicalCoordinateSupportedCone R).obj ≅
      CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map
          (unitMul _ (polynomialCoordinate R))) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso
      (tautologicalCoordinatePerfect R).hom (Scheme.Modules.restrictFunctor (minusChart R)) ≪≫
    CochainComplex.mappingCone.isoOfIso _ _ (tautologicalPerfectMinusIso R)
      ((locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (minusChart R)))
      (tautologicalCoordinatePerfect_minus R)

/-- The negative cone comparison retains the actual original cone inclusion of the target. -/
theorem tautologicalCoordinateConeMinusIso_inr (R : CommRingCat.{u}) :
    (restrict (minusChart R)).map
        (CochainComplex.mappingCone.inr (tautologicalCoordinatePerfect R).hom) ≫
      (tautologicalCoordinateConeMinusIso R).hom =
    ((locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (minusChart R))).hom ≫
      CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map
          (unitMul _ (polynomialCoordinate R))) := by
  have h := CochainComplex.mappingCone.map_inr (tautologicalCoordinatePerfect R).hom
    (Scheme.Modules.restrictFunctor (minusChart R))
  change (restrict (minusChart R)).map
      (CochainComplex.mappingCone.inr (tautologicalCoordinatePerfect R).hom) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (tautologicalCoordinatePerfect R).hom
        (Scheme.Modules.restrictFunctor (minusChart R))).hom = _ at h
  rw [tautologicalCoordinateConeMinusIso, Iso.trans_hom, ← Category.assoc, h]
  simp [CochainComplex.mappingCone.isoOfIso, CochainComplex.mappingCone.map]

private theorem unitMul_eq_globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    unitMul X r = (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app
      (SheafOfModules.unit X.ringCatSheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change x * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r =
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r * x
  exact mul_comm _ _

private theorem single_unitMul_eq_globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (CochainComplex.singleFunctor X.Modules 0).map (unitMul X r) =
      (complexGlobalScalar X r).app (rankOnePerfect X).obj := by
  apply HomologicalComplex.from_single_hom_ext
  change ((HomologicalComplex.single X.Modules (.up ℤ) 0).map (unitMul X r)).f 0 =
    (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app
      (((HomologicalComplex.single X.Modules (.up ℤ) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)).X 0)
  rw [HomologicalComplex.single_map_f_self, unitMul_eq_globalScalar]
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit X.ringCatSheaf)
  change e.hom ≫ (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app _ ≫ e.inv =
    (AlgebraicGeometry.Scheme.Modules.globalScalar X r).app _
  rw [← cancel_mono e.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ((AlgebraicGeometry.Scheme.Modules.globalScalar X r).naturality e.hom).symm

/-- The negative scalar single equals the original termwise global scalar on actual rank one. -/
theorem tautologicalNegativeScalar_eq_globalScalar (R : CommRingCat.{u}) :
    (CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map
        (unitMul _ (polynomialCoordinate R)) =
      (complexGlobalScalar _ (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialGlobalCoordinate
        R)).app
        (rankOnePerfect (Spec (.of (Polynomial R)))).obj :=
  single_unitMul_eq_globalScalar _ _

/-- The actual negative restriction is the cone of the original rank-one scalar, with no
replacement scalar or implicit single identification. -/
def tautologicalCoordinateConeMinusGlobalScalarIso (R : CommRingCat.{u}) :
    (restrict (minusChart R)).obj (tautologicalCoordinateSupportedCone R).obj ≅
      CochainComplex.mappingCone
        ((complexGlobalScalar _
          (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialGlobalCoordinate R)).app
            (rankOnePerfect (Spec (.of (Polynomial R)))).obj) :=
  tautologicalCoordinateConeMinusIso R ≪≫
    eqToIso (congrArg (fun f => CochainComplex.mappingCone f)
      (tautologicalNegativeScalar_eq_globalScalar R))

private theorem mappingCone_eqToIso_inr {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    {f g : K ⟶ L} (h : f = g) :
    CochainComplex.mappingCone.inr f ≫
        (eqToIso (congrArg (fun f => CochainComplex.mappingCone f) h)).hom =
      CochainComplex.mappingCone.inr g := by
  subst g
  simp

/-- The comparison with the original scalar cone preserves the actual target cone inclusion. -/
theorem tautologicalCoordinateConeMinusGlobalScalarIso_inr (R : CommRingCat.{u}) :
    (restrict (minusChart R)).map
        (CochainComplex.mappingCone.inr (tautologicalCoordinatePerfect R).hom) ≫
      (tautologicalCoordinateConeMinusGlobalScalarIso R).hom =
    ((locallyPerfect _).ι.mapIso (rankOnePerfectRestrictIso (minusChart R))).hom ≫
      CochainComplex.mappingCone.inr
        ((complexGlobalScalar _
          (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialGlobalCoordinate R)).app
            (rankOnePerfect (Spec (.of (Polynomial R)))).obj) := by
  rw [tautologicalCoordinateConeMinusGlobalScalarIso, Iso.trans_hom, ← Category.assoc,
    tautologicalCoordinateConeMinusIso_inr, Category.assoc,
    mappingCone_eqToIso_inr (tautologicalNegativeScalar_eq_globalScalar R)]

end Quillen.PerfectComplexes.ProjectiveLine
