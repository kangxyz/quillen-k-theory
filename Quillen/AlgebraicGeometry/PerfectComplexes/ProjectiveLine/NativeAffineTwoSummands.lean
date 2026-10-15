/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTwoSummandComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeAffineTautological
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.PullbackTensorCompatibility

/-!
# Original native affine two-summand correspondence

The actual affine geometry and tautological-line identification compare the
existing native O/O(-1) summands with the actual original two-chart summands.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.Bass
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-- The same original compact affine base used by nativeTwoSummands. -/
abbrev affineBase (R : CommRingCat.{u}) : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u} :=
  ⟨Spec R, inferInstance⟩

/-- Actual geometric transport from the native product line to the original two-chart line. -/
def nativeTransport (R : CommRingCat.{u}) :
    Perfect (nativeLineFunctor.obj (affineBase R)).obj ⥤ Perfect (twoChartLine R) :=
  perfectFlatPullback (nativeAffineIso R).hom

instance nativeTransport_additive (R : CommRingCat.{u}) : (nativeTransport R).Additive := by
  unfold nativeTransport
  infer_instance

lemma nativeTransport_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).cof
    (perfectWaldhausen (nativeLineFunctor.obj (affineBase R)).obj).weq
    (perfectWaldhausen (twoChartLine R)).cof (perfectWaldhausen (twoChartLine R)).weq
    (nativeTransport R) := perfectFlatPullback_waldhausenExact _

/-- The first original native summand retains the actual original affine projection. -/
def nativeFirstTransportIso (R : CommRingCat.{u}) :
    nativeFirstSummand (affineBase R) ⋙ nativeTransport R ≅
      perfectFlatPullback (projection R) :=
  (perfectFlatPullbackCompIso (nativeAffineIso R).hom
      (nativeProjection.app (affineBase R)).hom).symm ≪≫
    eqToIso (by congr 1; exact nativeAffineIso_projection R)

/-- The original pullback-tensor mate is invertible through the actual native line charts. -/
instance nativeLinePullbackTensorMap_isIso (R : CommRingCat.{u})
    (E : (nativeLineFunctor.obj (affineBase R)).obj.Modules) :
    IsIso (modulePullbackTensorMap (nativeAffineIso R).hom
      (nativeTautologicalLine (affineBase R)) E) := by
  apply modulePullbackTensorMap_isIso_of_trivializingCover (nativeAffineIso R).hom
    (fun _ : Bool => (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj
      (affineBase R)).obj)
    (nativeChart (affineBase R)) (nativeChart_cover (affineBase R))
    (nativeTautologicalLine (affineBase R)) E (nativeLineChartIso (affineBase R))

/-- The actual natural original pullback-tensor mate with the native line. -/
def nativeTwistPullbackModuleIso (R : CommRingCat.{u}) :
    moduleTensorLeftFunctor (nativeLineFunctor.obj (affineBase R)).obj
        (nativeTautologicalLine (affineBase R)) ⋙
          Scheme.Modules.pullback (nativeAffineIso R).hom ≅
      Scheme.Modules.pullback (nativeAffineIso R).hom ⋙
        moduleTensorLeftFunctor (twoChartLine R)
          ((Scheme.Modules.pullback (nativeAffineIso R).hom).obj
            (nativeTautologicalLine (affineBase R))) :=
  NatIso.ofComponents
    (fun E => asIso (modulePullbackTensorMap (nativeAffineIso R).hom
      (nativeTautologicalLine (affineBase R)) E))
    (fun f => modulePullbackTensorMap_naturality_right (nativeAffineIso R).hom _ f)

/-- Actual natural tensor transport, followed by the actual affine tautological identification. -/
def nativeTwistTransportModuleIso (R : CommRingCat.{u}) :
    moduleTensorLeftFunctor (nativeLineFunctor.obj (affineBase R)).obj
        (nativeTautologicalLine (affineBase R)) ⋙
          Scheme.Modules.pullback (nativeAffineIso R).hom ≅
      Scheme.Modules.pullback (nativeAffineIso R).hom ⋙
        moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R) :=
  nativeTwistPullbackModuleIso R ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback (nativeAffineIso R).hom)
      ((SheafOfModulesOfCommRing.tensorFunctor (twoChartLine R).sheaf).mapIso
        (nativeAffineTautologicalIso R))

/-- The actual sheaf tensor transport gives a natural original chain isomorphism. -/
def nativeTwistTransportComplexIso (R : CommRingCat.{u}) :
    tensorByLineComplex (nativeTautologicalLine (affineBase R)) ⋙
        pullbackComplex (nativeAffineIso R).hom ≅
      pullbackComplex (nativeAffineIso R).hom ⋙ tensorByLineComplex (tautologicalLine R) :=
  Functor.mapHomologicalComplexCompIso (nativeTwistTransportModuleIso R) (.up ℤ)

/-- The transported native negative twist is the actual local negative twist. -/
def nativeTwistTransportIso (R : CommRingCat.{u}) :
    nativeNegativeTwist (affineBase R) ⋙ nativeTransport R ≅
      nativeTransport R ⋙ localNegativeTwist R :=
  Functor.fullyFaithfulCancelRight (locallyPerfect (twoChartLine R)).ι
    (Functor.isoWhiskerLeft (locallyPerfect (nativeLineFunctor.obj (affineBase R)).obj).ι
      (nativeTwistTransportComplexIso R))

/-- The second native summand retains the actual affine negative line and original tensor. -/
def nativeSecondTransportIso (R : CommRingCat.{u}) :
    nativeSecondSummand (affineBase R) ⋙ nativeTransport R ≅
      perfectFlatPullback (projection R) ⋙ localNegativeTwist R :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (nativeFirstSummand (affineBase R)) (nativeTwistTransportIso R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (nativeFirstTransportIso R) (localNegativeTwist R)

instance nativeTransport_preservesBinaryCoproducts (R : CommRingCat.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (nativeTransport R) := by
  let : PreservesBinaryBiproducts (nativeTransport R) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact preservesBinaryCoproducts_of_preservesBinaryBiproducts _

/-- Actual additive comparison for transport of the original selected coproduct. -/
def sumPostcomposeIso {C : Type v} [Category C] {D E : Type w} [Category D] [Category E]
    [HasBinaryCoproducts D] [HasBinaryCoproducts E] (H F : C ⥤ D) (J : D ⥤ E)
    [PreservesColimitsOfShape (Discrete WalkingPair) J] :
    Waldhausen.Additivity.sumFunctor H F ⋙ J ≅
      Waldhausen.Additivity.sumFunctor (H ⋙ J) (F ⋙ J) :=
  (NatIso.ofComponents
    (fun K => asIso (coprodComparison J (H.obj K) (F.obj K)))
    (fun f => (coprodComparison_natural J (H.map f) (F.map f)).symm)).symm

/-- Actual natural coproduct of two original natural summand identifications. -/
def sumIso {C : Type v} [Category C] {D : Type w} [Category D] [HasBinaryCoproducts D]
    {H H' F F' : C ⥤ D} (eH : H ≅ H') (eF : F ≅ F') :
    Waldhausen.Additivity.sumFunctor H F ≅ Waldhausen.Additivity.sumFunctor H' F' :=
  NatIso.ofComponents (fun K => coprod.mapIso (eH.app K) (eF.app K)) (by
    intro K L f
    change coprod.map (H.map f) (F.map f) ≫ coprod.map (eH.hom.app L) (eF.hom.app L) =
      coprod.map (eH.hom.app K) (eF.hom.app K) ≫ coprod.map (H'.map f) (F'.map f)
    rw [coprod.map_map, coprod.map_map, eH.hom.naturality, eF.hom.naturality])

/-- The EXISTING original nativeTwoSummands, transported by the actual affine scheme isomorphism. -/
def nativeTwoSummandsTransportIso (R : CommRingCat.{u}) :
    nativeTwoSummands (affineBase R) ⋙ nativeTransport R ≅ localTwoSummands R :=
  sumPostcomposeIso
      (CategoryTheory.Prod.fst _ _ ⋙ nativeFirstSummand (affineBase R))
      (CategoryTheory.Prod.snd _ _ ⋙ nativeSecondSummand (affineBase R)) (nativeTransport R) ≪≫
    sumIso (Functor.isoWhiskerLeft (CategoryTheory.Prod.fst _ _) (nativeFirstTransportIso R))
      (Functor.isoWhiskerLeft (CategoryTheory.Prod.snd _ _) (nativeSecondTransportIso R))

/-- Exact original-map correspondence to the existing native functor, in every natural degree. -/
lemma localTwoSummands_KMap_native (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (localTwoSummands_exact R) n =
      (Waldhausen.KMap (nativeTransport_exact R) n).comp
        (Waldhausen.KMap (nativeTwoSummands_exact (affineBase R)) n) := by
  rw [Waldhausen.KMap_comp_KMap]
  exact (Waldhausen.KMap_eq_of_iso
    ((nativeTwoSummands_exact (affineBase R)).comp (nativeTransport_exact R))
    (localTwoSummands_exact R) (nativeTwoSummandsTransportIso R) n).symm

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
