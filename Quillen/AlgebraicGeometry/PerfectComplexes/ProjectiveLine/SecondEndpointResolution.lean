/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.ProjectionFormula
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.NatTransQuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeModel

/-!
# Literal second diagonal vertex and the original projection-formula weak legs

The second coefficient retains its original right tensor. The original
coefficient symmetry followed by left tensor of the original first-pullback
augmentation gives the resolved coefficient map. Original total and ordinary
second image preserve this map between the actual flasque totals.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
open FlasqueCoefficients

/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance standardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u})

/-- Original left tensor on the square by the actual second pullback of Q. -/
abbrev squareTensor : (relativeSquare R).Modules ⥤ (relativeSquare R).Modules :=
  moduleTensorLeftFunctor (relativeSquare R)
    ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R))

/-- Original first pullback of the literal input complex. -/
def firstPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (relativeSquare R).Modules :=
  toPlus (twoChartLine R) ⋙ (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus

/-- The actual flasque complex C=T_Z(p1* K). -/
def CPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (relativeSquare R).Modules :=
  firstPlus R ⋙ godementTotalPlus (relativeSquare R)

/-- The actual ordinary U=p2_* C, before tensor or any outer total. -/
def UPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (twoChartLine R).Modules :=
  CPlus R ⋙ (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus

/-- The literal middle value V=p2_* T_Z(p2*Q tensor C). -/
def VPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (twoChartLine R).Modules :=
  CPlus R ⋙ (squareTensor R).mapCochainComplexPlus ⋙
    godementTotalPlus (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus

/-- Original left Q tensor U, retaining the original tensor order. -/
def tensorUPlus : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    CochainComplex.Plus (twoChartLine R).Modules :=
  UPlus R ⋙ (moduleTensorLeftFunctor (twoChartLine R)
    (tautologicalQuotientLine R)).mapCochainComplexPlus

/-- The exact ORIGINAL coefficient braiding from p1*K right tensor p2*Q. -/
def coefficientLeftIso : FlasqueDiagonal.coefficient R .second ≅
    Scheme.Modules.pullback (relativeFirst R) ⋙ squareTensor R :=
  isoWhiskerLeft (Scheme.Modules.pullback (relativeFirst R))
    (moduleTensorSymmetryNatIso (relativeSquare R)
      ((Scheme.Modules.pullback (relativeSecond R)).obj (tautologicalQuotientLine R)))

/-- Original coefficient braiding on the actual bounded-below chain maps. -/
def coefficientLeftPlusIso :
    (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus ≅
      (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus ⋙
        (squareTensor R).mapCochainComplexPlus :=
  NatIso.mapCochainComplexPlus (coefficientLeftIso R) ≪≫
    mapCochainComplexPlusCompIso (Scheme.Modules.pullback (relativeFirst R)) (squareTensor R)

/-- The ORIGINAL braiding, then original left tensor of the actual augmentation. -/
def coefficientResolutionMap :
    toPlus (twoChartLine R) ⋙
        (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus ⟶
      CPlus R ⋙ (squareTensor R).mapCochainComplexPlus :=
  whiskerLeft (toPlus (twoChartLine R)) (coefficientLeftPlusIso R).hom ≫
    whiskerRight (whiskerLeft (firstPlus R) (godementTotalPlusUnit (relativeSquare R)))
      (squareTensor R).mapCochainComplexPlus

/-- Literal C before forgetting its strict lower-bound witness. -/
def CRaw : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex (relativeSquare R).Modules ℤ :=
  CPlus R ⋙ CochainComplex.Plus.ι (relativeSquare R).Modules

/-- Literal V before any outer total, forgetting only the strict lower-bound witness. -/
def VRaw : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex (twoChartLine R).Modules ℤ :=
  VPlus R ⋙ CochainComplex.Plus.ι (twoChartLine R).Modules

/-- Original resolved-coefficient naturality in the actual original chain category. -/
lemma coefficientResolutionMap_naturality_hom
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    ((toPlus (twoChartLine R) ⋙
        (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus).map a).hom ≫
      ((coefficientResolutionMap R).app L).hom =
    ((coefficientResolutionMap R).app K).hom ≫
      ((CPlus R ⋙ (squareTensor R).mapCochainComplexPlus).map a).hom :=
  congrArg (CochainComplex.Plus.ι (relativeSquare R).Modules).map
    ((coefficientResolutionMap R).naturality a)

lemma coefficientResolutionMap_source_map_hom
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    ((toPlus (twoChartLine R) ⋙
        (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus).map a).hom =
      ((FlasqueDiagonal.coefficient R .second).mapHomologicalComplex (.up ℤ)).map a.hom := rfl

/-- Canonical associators retain the actual total/image order without structural casts. -/
@[irreducible] def rightPlusMap : FlasqueDiagonal.rawPlus R .second ⟶ VPlus R := by
  dsimp only [FlasqueDiagonal.rawPlus, VPlus]
  exact plusReassociatedTotalImageMap (relativeSecond R)
    (toPlus (twoChartLine R))
    (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus
    (CPlus R) (squareTensor R).mapCochainComplexPlus (coefficientResolutionMap R)

/-- The original ordinary projection formula followed by pushed original augmentation. -/
def beta : tensorUPlus R ⟶ VPlus R :=
  whiskerLeft (CPlus R)
    (godementProjectionFormulaMap (relativeSecond R) (tautologicalQuotientLine R))

lemma firstPlus_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((firstPlus R).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pullback (relativeFirst R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

lemma CPlus_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((CPlus R).obj K).obj.IsStrictlyGE a := by
  let B := (firstPlus R).obj K
  let : B.obj.IsStrictlyGE a := firstPlus_isStrictlyGE R K a
  exact godementTotal_isStrictlyGE B.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE B.obj a n hn)

lemma CPlus_flasque (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((CPlus R).obj K).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  let B := (firstPlus R).obj K
  let : B.obj.IsStrictlyGE a := firstPlus_isStrictlyGE R K a
  exact godementTotal_isFlasque B.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE B.obj a i hi) n

lemma UPlus_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((UPlus R).obj K).obj.IsStrictlyGE a := by
  let : ((CPlus R).obj K).obj.IsStrictlyGE a := CPlus_isStrictlyGE R K a
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (relativeSecond R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE ((CPlus R).obj K).obj a n hn)

lemma UPlus_flasque (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((UPlus R).obj K).obj.X n).presheaf := by
  let : TopCat.Presheaf.IsFlasque (((CPlus R).obj K).obj.X n).presheaf :=
    CPlus_flasque R K n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (relativeSecond R)).obj
      (((CPlus R).obj K).obj.X n)).presheaf
  infer_instance

/-- Left tensor preserves the input bound; no flasqueness is asserted for this tensor. -/
lemma tensorCPlus_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((squareTensor R).mapCochainComplexPlus.obj ((CPlus R).obj K)).obj.IsStrictlyGE a := by
  let : ((CPlus R).obj K).obj.IsStrictlyGE a := CPlus_isStrictlyGE R K a
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (squareTensor R).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE ((CPlus R).obj K).obj a n hn)

lemma VPlus_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((VPlus R).obj K).obj.IsStrictlyGE a := by
  let B := (squareTensor R).mapCochainComplexPlus.obj ((CPlus R).obj K)
  let : B.obj.IsStrictlyGE a := tensorCPlus_isStrictlyGE R K a
  let : ((godementTotalPlus (relativeSquare R)).obj B).obj.IsStrictlyGE a :=
    godementTotal_isStrictlyGE B.obj a
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE B.obj a n hn)
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (relativeSecond R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE
      ((godementTotalPlus (relativeSquare R)).obj B).obj a n hn)

lemma VPlus_flasque (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((VPlus R).obj K).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  let B := (squareTensor R).mapCochainComplexPlus.obj ((CPlus R).obj K)
  let : B.obj.IsStrictlyGE a := tensorCPlus_isStrictlyGE R K a
  let : TopCat.Presheaf.IsFlasque
      (((godementTotalPlus (relativeSquare R)).obj B).obj.X n).presheaf :=
    godementTotal_isFlasque B.obj a
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE B.obj a i hi) n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (relativeSecond R)).obj
      (((godementTotalPlus (relativeSquare R)).obj B).obj.X n)).presheaf
  infer_instance

/-- The coefficient resolution is weak by exact left tensor of the original weak unit. -/
lemma coefficientResolutionMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((coefficientResolutionMap R).app K).hom := by
  let B := (firstPlus R).obj K
  let e := (coefficientLeftPlusIso R).hom.app ((toPlus (twoChartLine R)).obj K)
  let t := (squareTensor R).mapCochainComplexPlus.map
    ((godementTotalPlusUnit (relativeSquare R)).app B)
  let : IsIso e.hom := Functor.map_isIso (CochainComplex.Plus.ι (relativeSquare R).Modules) e
  let : QuasiIso e.hom := inferInstance
  let : QuasiIso t.hom := by
    change QuasiIso (((squareTensor R).mapHomologicalComplex (.up ℤ)).map
      ((godementTotalPlusUnit (relativeSquare R)).app B).hom)
    infer_instance
  change QuasiIso (e.hom ≫ t.hom)
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
/-- Only original direct image BETWEEN THE TWO ACTUAL FLASQUE TOTALS is used. -/
lemma rightPlusMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) ((rightPlusMap R).app K) := by
  unfold rightPlusMap
  exact plusReassociatedTotalImageMap_quasiIso (relativeSecond R)
    (toPlus (twoChartLine R))
    (FlasqueDiagonal.coefficient R .second).mapCochainComplexPlus
    (CPlus R) (squareTensor R).mapCochainComplexPlus
    (coefficientResolutionMap R) (coefficientResolutionMap_quasiIso R) K

/-- The literal beta component is weak through the proved ORIGINAL derived projection mate. -/
lemma beta_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((beta R).app K).hom :=
  godementProjectionFormulaMap_quasiIso (relativeSecond R) (tautologicalQuotientLine R)
    ((CPlus R).obj K) (CPlus_flasque R K)

/-- The localized beta is the original finite-line derived projection formula, with all
installed units and the actual total comparison in their original order. -/
lemma beta_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (beta R).app K = (godementProjectionFormulaMap (relativeSecond R)
      (tautologicalQuotientLine R)).app ((CPlus R).obj K) := rfl

lemma beta_derived (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    DerivedCategory.Plus.Q.map
        ((godementProjectionFormulaMap (relativeSecond R)
          (tautologicalQuotientLine R)).app ((CPlus R).obj K)) ≫
        godementProjectionFormulaTargetComparison (relativeSecond R)
          (tautologicalQuotientLine R) ((CPlus R).obj K) =
      godementProjectionFormulaSourceComparison (relativeSecond R)
          (tautologicalQuotientLine R) ((CPlus R).obj K) ≫
        (derivedProjectionFormulaIso (relativeSecond R)
          (tautologicalQuotientLine R)).hom.app (DerivedCategory.Plus.Q.obj ((CPlus R).obj K)) :=
  godementProjectionFormulaMap_derived (relativeSecond R) (tautologicalQuotientLine R)
    ((CPlus R).obj K)

end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
