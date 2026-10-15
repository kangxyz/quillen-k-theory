/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Native
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor
public import Quillen.Waldhausen.Additivity.GroupFormula

/-! # The actual native two-summand exact functor and chart maps

For arbitrary quasi-compact schemes, the functor is the coproduct of actual
flat pullback and actual negative-line tensor of flat pullback. The tensor
convention puts the fixed line on the left. Both original chart restrictions
are naturally identified with native polynomial pullback on each summand.
The induced original K-map therefore has the sum chart formula in every
nonnegative degree, including zero. Bijectivity is not asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.Waldhausen.ExtensionCategory

/-- Boolean indexing of the two original native chart maps. -/
def nativeChart (X : QuasiCompactSchemes.{u}) (b : Bool) :
    (polynomialFunctor.obj X).obj ⟶ (nativeLineFunctor.obj X).obj :=
  if b then (nativePlus.app X).hom else (nativeMinus.app X).hom

instance nativeChart_isOpenImmersion (X : QuasiCompactSchemes.{u}) (b : Bool) :
    IsOpenImmersion (nativeChart X b) := by
  cases b <;> dsimp [nativeChart] <;> infer_instance

/-- Both actual native chart maps retain the original projection. -/
@[reassoc (attr := simp)]
theorem nativeChart_projection (X : QuasiCompactSchemes.{u}) (b : Bool) :
    nativeChart X b ≫ (nativeProjection.app X).hom =
      (PolynomialLaurent.Relative.polynomialProjection.app X).hom := by
  cases b
  · exact congrArg (fun f => f.hom) (nativeMinus_projection X)
  · exact congrArg (fun f => f.hom) (nativePlus_projection X)

/-- The actual chart family is a covering family. -/
theorem nativeChart_cover (X : QuasiCompactSchemes.{u})
    (x : (nativeLineFunctor.obj X).obj) :
    ∃ b y, nativeChart X b y = x := by
  rcases native_charts_cover X x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨true, y, hy⟩
  · exact ⟨false, y, hy⟩

/-- Original tautological chart trivializations, indexed by the original chart choice. -/
def nativeLineChartIso (X : QuasiCompactSchemes.{u}) (b : Bool) :
    (nativeTautologicalLine X).restrict (nativeChart X b) ≅
      SheafOfModules.unit (polynomialFunctor.obj X).obj.ringCatSheaf := by
  cases b
  · exact nativeTautologicalMinusIso X
  · exact nativeTautologicalPlusIso X

/-- Exact tensor with the actual native negative line on arbitrary locally perfect complexes. -/
def nativeNegativeTwist (X : QuasiCompactSchemes.{u}) :
    Perfect (nativeLineFunctor.obj X).obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  perfectTensorByLine (nativeTautologicalLine X)
    (fun _ : Bool => (polynomialFunctor.obj X).obj) (nativeChart X)
    (nativeChart_cover X) (nativeLineChartIso X)

theorem nativeNegativeTwist_exact (X : QuasiCompactSchemes.{u}) :
    IsExact (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (nativeNegativeTwist X) :=
  perfectTensorByLine_waldhausenExact _ _ _ _ _

/-- Negative-line tensor is canonically trivial on each actual native chart. -/
def nativeNegativeTwistChartIso (X : QuasiCompactSchemes.{u}) (b : Bool) :
    nativeNegativeTwist X ⋙ perfectRestrict (nativeChart X b) ≅
      perfectRestrict (nativeChart X b) :=
  perfectTensorByLineChartIso _ _ _ _ _ b

/-- The original structure-line summand. -/
def nativeFirstSummand (X : QuasiCompactSchemes.{u}) :
    Perfect X.obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  perfectFlatPullback (nativeProjection.app X).hom

/-- The original negative-line summand, using exact degreewise tensor. -/
def nativeSecondSummand (X : QuasiCompactSchemes.{u}) :
    Perfect X.obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  nativeFirstSummand X ⋙ nativeNegativeTwist X

/-- The second summand is the prescribed pullback tensor O(-1), through actual symmetry. -/
def nativeSecondSummandTensorOrderIso (X : QuasiCompactSchemes.{u}) (B : Perfect X.obj) :
    ((nativeSecondSummand X).obj B).obj ≅
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (nativeTautologicalLine X)).obj
        ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (nativeProjection.app X).hom).obj B.obj)
          :=
  (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftRightIso (nativeTautologicalLine X)).app _

theorem nativeFirstSummand_exact (X : QuasiCompactSchemes.{u}) :
    IsExact (perfectWaldhausen X.obj).cof (perfectWaldhausen X.obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (nativeFirstSummand X) :=
  perfectFlatPullback_waldhausenExact _

theorem nativeSecondSummand_exact (X : QuasiCompactSchemes.{u}) :
    IsExact (perfectWaldhausen X.obj).cof (perfectWaldhausen X.obj).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (nativeSecondSummand X) :=
  (nativeFirstSummand_exact X).comp (nativeNegativeTwist_exact X)

/-- Actual chart restriction of the structure-line summand is native polynomial pullback. -/
def nativeFirstSummandChartIso (X : QuasiCompactSchemes.{u}) (b : Bool) :
    nativeFirstSummand X ⋙ perfectRestrict (nativeChart X b) ≅
      perfectFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom :=
  Functor.isoWhiskerLeft (nativeFirstSummand X)
      (perfectRestrictIsoFlatPullback (nativeChart X b)) ≪≫
    (perfectFlatPullbackCompIso (nativeChart X b) (nativeProjection.app X).hom).symm ≪≫
    eqToIso (by congr 1; exact nativeChart_projection X b)

/-- Actual chart restriction of the negative-line summand is the same polynomial pullback. -/
def nativeSecondSummandChartIso (X : QuasiCompactSchemes.{u}) (b : Bool) :
    nativeSecondSummand X ⋙ perfectRestrict (nativeChart X b) ≅
      perfectFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (nativeFirstSummand X) (nativeNegativeTwistChartIso X b) ≪≫
    nativeFirstSummandChartIso X b

/-- The actual two-summand perfect functor, in the order O, O(-1). -/
def nativeTwoSummands (X : QuasiCompactSchemes.{u}) :
    Perfect X.obj × Perfect X.obj ⥤ Perfect (nativeLineFunctor.obj X).obj :=
  Additivity.sumFunctor
    (CategoryTheory.Prod.fst _ _ ⋙ nativeFirstSummand X)
    (CategoryTheory.Prod.snd _ _ ⋙ nativeSecondSummand X)

/-- No generation premise is needed for exactness of the actual two-summand functor. -/
theorem nativeTwoSummands_exact (X : QuasiCompactSchemes.{u}) :
    IsExact (productStructure (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).cof
      (productStructure (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).weq
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).cof
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq (nativeTwoSummands X) :=
  Additivity.sumFunctor_isExact _ _
    ((fst_exact _ _).comp (nativeFirstSummand_exact X))
    ((snd_exact _ _).comp (nativeSecondSummand_exact X))

/-- The original induced K-map after the original product K-equivalence. -/
def nativeTwoSummandKMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    PerfectK X.obj n × PerfectK X.obj n →* PerfectK (nativeLineFunctor.obj X).obj n :=
  (KMap (nativeTwoSummands_exact X) n).comp
    (Product.KEquiv (perfectWaldhausen X.obj) (perfectWaldhausen X.obj) n).symm.toMonoidHom

/-- The original group law records precisely the two actual summand K-maps. -/
theorem nativeTwoSummandKMap_apply (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a b : PerfectK X.obj n) :
    nativeTwoSummandKMap X n (a, b) =
      KMap (nativeFirstSummand_exact X) n a * KMap (nativeSecondSummand_exact X) n b := by
  let z := (Product.KEquiv (perfectWaldhausen X.obj) (perfectWaldhausen X.obj) n).symm (a, b)
  have hz : (KMap (fst_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)) n z,
      KMap (snd_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)) n z) = (a, b) :=
    (Product.KEquiv (perfectWaldhausen X.obj) (perfectWaldhausen X.obj) n).apply_symm_apply _
  change KMap (nativeTwoSummands_exact X) n z = _
  rw [Additivity.KMap_sum_apply _ _
    ((fst_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).comp
      (nativeFirstSummand_exact X))
    ((snd_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).comp
      (nativeSecondSummand_exact X))]
  rw [← KMap_comp_KMap (fst_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj))
      (nativeFirstSummand_exact X),
    ← KMap_comp_KMap (snd_exact (perfectWaldhausen X.obj) (perfectWaldhausen X.obj))
      (nativeSecondSummand_exact X)]
  change KMap (nativeFirstSummand_exact X) n _ * KMap (nativeSecondSummand_exact X) n _ = _
  exact congrArg₂ (fun x y => KMap (nativeFirstSummand_exact X) n x *
    KMap (nativeSecondSummand_exact X) n y)
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz)

/-- The actual first-summand restriction equation in every original nonnegative K-group. -/
theorem nativeFirstSummandKMap_chart (X : QuasiCompactSchemes.{u}) (b : Bool) (n : ℕ) :
    (perfectKRestrict (nativeChart X b) n).comp (KMap (nativeFirstSummand_exact X) n) =
      perfectKFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom n := by
  rw [perfectKRestrict, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeFirstSummandChartIso X b) n

/-- The negative-line summand has exactly the same original restriction map. -/
theorem nativeSecondSummandKMap_chart (X : QuasiCompactSchemes.{u}) (b : Bool) (n : ℕ) :
    (perfectKRestrict (nativeChart X b) n).comp (KMap (nativeSecondSummand_exact X) n) =
      perfectKFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom n := by
  rw [perfectKRestrict, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (nativeSecondSummandChartIso X b) n

/-- Both original chart restrictions have the literal sum matrix, including K₀. -/
theorem nativeTwoSummandKMap_chart (X : QuasiCompactSchemes.{u}) (b : Bool) (n : ℕ)
    (a c : PerfectK X.obj n) :
    perfectKRestrict (nativeChart X b) n (nativeTwoSummandKMap X n (a, c)) =
      perfectKFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom n a *
        perfectKFlatPullback (PolynomialLaurent.Relative.polynomialProjection.app X).hom n c := by
  rw [nativeTwoSummandKMap_apply, map_mul]
  exact congrArg₂ (· * ·)
    (DFunLike.congr_fun (nativeFirstSummandKMap_chart X b n) a)
    (DFunLike.congr_fun (nativeSecondSummandKMap_chart X b n) c)

end Quillen.PerfectComplexes.ProjectiveLine
