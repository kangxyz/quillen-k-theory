/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SecondEndpointAlignment
public import Quillen.Waldhausen.Functoriality.KMap

/-!
# The original natural weak second endpoint model span

The literal left map is total of original Q-tensored alpha followed by original beta.
The literal right map is original coefficient resolution followed by the forward V unit.
The native chosen-zero weak-transformation theorem compares the two original K-maps.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
variable (R : CommRingCat.{u})

/-- Original left Q tensor of the actual original alpha target, before outer total. -/
def tensorTargetBounded : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    BoundedBelow.Obj (twoChartLine R) :=
  (SelfBaseChange.target R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R)) ⋙
    quotientLeftBounded R

/-- The actual alpha, acted on by the original exact left Q tensor. -/
def tensorAlpha : sourceBounded R ⟶ tensorTargetBounded R :=
  whiskerRight (SelfBaseChange.alpha R) (quotientLeftBounded R)

lemma tensorAlpha_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((tensorAlpha R).app K).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalQuotientLine R)).map
        ((SelfBaseChange.alpha R).app K).hom := rfl

lemma tensorAlpha_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((tensorAlpha R).app K) :=
  (quotientLeftBounded_exact R).weak _ (SelfBaseChange.alpha_weak R K)

/-- Original beta lifted to the original bounded model, retaining its actual comparison. -/
def betaBounded : tensorTargetBounded R ⟶
    V R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) where
  app K := ObjectProperty.homMk ((betaRaw R).app K)
  naturality {K L} a := by
    apply ObjectProperty.hom_ext
    exact (betaRaw R).naturality a

lemma betaBounded_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((betaBounded R).app K).hom = (betaRaw R).app K := rfl

lemma betaBounded_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((betaBounded R).app K) :=
  betaRaw_quasiIso R K

/-- The entire original pre-total left chain, in the required order. -/
def preLeftMap : sourceBounded R ⟶
    V R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) :=
  tensorAlpha R ≫ betaBounded R

lemma preLeftMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((preLeftMap R).app K).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalQuotientLine R)).map
        ((SelfBaseChange.alpha R).app K).hom ≫
      (tensorUUnderlyingIso R).inv.app K ≫ ((beta R).app K).hom := rfl

lemma preLeftMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((preLeftMap R).app K) :=
  (BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    (tensorAlpha_weak R K) (betaBounded_weak R K)

/-- Literal outer total of the full original left chain, with every actual component retained. -/
def spanLeftMap : source R ⟶ center R where
  app K := (FlasqueBoundedBelow.total (twoChartLine R)).map ((preLeftMap R).app K)
  naturality {K L} a := by
    exact (whiskerRight (preLeftMap R)
      (FlasqueBoundedBelow.total (twoChartLine R))).naturality a

lemma spanLeftMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((spanLeftMap R).app K).hom =
      (godementTotal (twoChartLine R)).map ((preLeftMap R).app K).hom := rfl

lemma spanLeftMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanLeftMap R).app K) :=
  FlasqueBoundedBelow.total_weak _ (preLeftMap_weak R K)

/-- The actual original right coefficient-resolution map lifted to the flasque model. -/
def rightToV : FlasqueDiagonal.E R .second ⟶ V R where
  app K := ObjectProperty.homMk ((rightRawMap R).app K)
  naturality {K L} a := by
    apply ObjectProperty.hom_ext
    exact (rightRawMap R).naturality a

lemma rightToV_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((rightToV R).app K).hom = (rightRawMap R).app K := rfl

lemma rightToV_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((rightToV R).app K) :=
  rightRawMap_quasiIso R K

/-- The original forward augmentation on actual V, with the installed total and inclusion. -/
def VUnit : V R ⟶ center R :=
  whiskerLeft (V R) (FlasqueBoundedBelow.flasqueUnit (twoChartLine R))

lemma VUnit_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((VUnit R).app K).hom =
      (godementTotalUnit (twoChartLine R)).app ((VRaw R).obj K) := rfl

lemma VUnit_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((VUnit R).app K) :=
  FlasqueBoundedBelow.flasqueUnit_weak (twoChartLine R) ((V R).obj K)

/-- The complete original right chain: actual coefficient resolution, then forward V unit. -/
def spanRightMap : FlasqueDiagonal.E R .second ⟶ center R :=
  rightToV R ≫ VUnit R

lemma spanRightMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((spanRightMap R).app K).hom = (rightRawMap R).app K ≫
      (godementTotalUnit (twoChartLine R)).app ((VRaw R).obj K) := rfl

lemma spanRightMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanRightMap R).app K) :=
  (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    (rightToV_weak R K) (VUnit_weak R K)

lemma spanLeftMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    (source R).map a ≫ (spanLeftMap R).app L =
      (spanLeftMap R).app K ≫ (center R).map a := (spanLeftMap R).naturality a

lemma spanRightMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    (FlasqueDiagonal.E R .second).map a ≫ (spanRightMap R).app L =
      (spanRightMap R).app K ≫ (center R).map a := (spanRightMap R).naturality a

lemma source_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    ((source R).map a).hom = (godementTotal (twoChartLine R)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalQuotientLine R)).map
        ((SelfBaseChange.source R).map a).hom) := rfl

lemma center_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    ((center R).map a).hom = (godementTotal (twoChartLine R)).map ((VRaw R).map a) := rfl

/-- The actual weak span compares the original canonical chosen-zero K-maps in every degree. -/
lemma KMap_source_eq_second (n : ℕ) :
    Waldhausen.KMap (source_exact R) n = Waldhausen.KMap (FlasqueDiagonal.E_exact R .second) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (source_exact R) (center_exact R)
    (spanLeftMap R) (spanLeftMap_weak R) n).trans
    (Waldhausen.KMap_eq_of_weakNatTrans (FlasqueDiagonal.E_exact R .second) (center_exact R)
      (spanRightMap R) (spanRightMap_weak R) n).symm

end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
