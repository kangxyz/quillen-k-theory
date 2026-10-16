/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.Pullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleComplexDirectImage
public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total
public import Quillen.Waldhausen.Functoriality.KMap

/-!
# Canonical positive retraction on strict affine coefficients

The positive functor is actual pullback, original Godement totalization, and
original degreewise direct image. The original geometric unit followed by the
direct image of the actual augmentation is naturally a quasi-isomorphism on
strict affine complexes. Applying the actual base totalization yields a weak
natural span inside the original flasque model and equality of original K-maps.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.Modules.Godement

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction

/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance positiveStandard (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- Literal inclusion of the original strict complex into the lower-bounded model. -/
def strictToBoundedBelow (X : Scheme.{u}) : StrictPerfect X ⥤ BoundedBelow.Obj X :=
  ObjectProperty.ιOfLE (fun K hK => by
    obtain ⟨a, b, h⟩ := hK.1
    exact ⟨locallyPerfect_of_strictPerfect hK, a,
      (CochainComplex.isStrictlyGE_iff K a).mpr (fun i hi => h i (Or.inl hi))⟩)

/-- The literal inclusion is exact for the original quotient-bearing cofibrations. -/
lemma strictToBoundedBelow_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (strictWaldhausen X).cof (strictWaldhausen X).weq
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq
    (strictToBoundedBelow X) :=
  Waldhausen.subcategoryInclusion_exact _ _ _

/-- Actual base Godement totalization of the original strict source complex. -/
def strictTotal (X : Scheme.{u}) : StrictPerfect X ⥤ FlasqueBoundedBelow.Obj X :=
  strictToBoundedBelow X ⋙ FlasqueBoundedBelow.total X

lemma strictTotal_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (strictWaldhausen X).cof (strictWaldhausen X).weq
    (FlasqueBoundedBelow.waldhausen X).cof (FlasqueBoundedBelow.waldhausen X).weq
    (strictTotal X) :=
  (strictToBoundedBelow_exact X).comp (FlasqueBoundedBelow.total_exact X)

/-- Actual pullback followed by the actual totalization on the original line. -/
def pullbackTotal (R : CommRingCat.{u}) :
    StrictPerfect (Spec R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  strictPullback (projection R) ⋙ strictTotal (twoChartLine R)

lemma pullbackTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (pullbackTotal R) :=
  (strictPullback_waldhausenExact (projection R)).comp (strictTotal_exact (twoChartLine R))

/-- The positive coefficient is literal p-star, Godement total, and p-sub-star. -/
def positive (R : CommRingCat.{u}) :
    StrictPerfect (Spec R) ⥤ FlasqueBoundedBelow.Obj (Spec R) :=
  pullbackTotal R ⋙ FlasqueCoefficients.G0 R

lemma positive_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (positive R) :=
  (pullbackTotal_exact R).comp (FlasqueCoefficients.G0_exact R)

/-- The actual positive construction on bounded-below ambient complexes. -/
def positivePlus (R : CommRingCat.{u}) :
    CochainComplex.Plus (Spec R).Modules ⥤ CochainComplex.Plus (Spec R).Modules :=
  (Scheme.Modules.pullback (projection R)).mapCochainComplexPlus ⋙
    godementTotalPlus (twoChartLine R) ⋙
      (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus

/-- The original degreewise geometric adjunction unit as an actual natural transformation. -/
def geometricPlusUnit (R : CommRingCat.{u}) :
    𝟭 (CochainComplex.Plus (Spec R).Modules) ⟶
      (Scheme.Modules.pullback (projection R)).mapCochainComplexPlus ⋙
        (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus where
  app K := projectionPullbackComplexUnit R K
  naturality {_ _} f := projectionPullbackComplexUnit_naturality R f

/-- Literal geometric unit followed by p-sub-star of the original Godement augmentation. -/
def positivePlusUnit (R : CommRingCat.{u}) :
    𝟭 (CochainComplex.Plus (Spec R).Modules) ⟶ positivePlus R :=
  geometricPlusUnit R ≫ CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerLeft
      (Scheme.Modules.pullback (projection R)).mapCochainComplexPlus
      (godementTotalPlusUnit (twoChartLine R)))
    (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus

/-- Both original constituent chain maps are retained by the canonical positive unit. -/
lemma positivePlusUnit_app (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) :
    (positivePlusUnit R).app K = projectionPullbackComplexUnit R K ≫
      (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.map
        ((godementTotalPlusUnit (twoChartLine R)).app
          ((Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj K)) := rfl

/-- Naturality of the installed derived unit proves the literal pushed augmentation is weak. -/
lemma pushforward_augmentation_isIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    IsIso (DerivedCategory.Plus.Q.map
      ((Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus.map
        ((godementTotalPlusUnit (twoChartLine R)).app
          ((Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj K)))) := by
  let C := (Scheme.Modules.pullback (projection R)).mapCochainComplexPlus.obj K
  let η := (godementTotalPlusUnit (twoChartLine R)).app C
  let F := (Scheme.Modules.pushforward (projection R)).mapCochainComplexPlus
  let U := derivedPushforwardPlusUnit (projection R)
  have : IsIso (DerivedCategory.Plus.Q.map η) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (twoChartLine R).Modules) _
      (godementTotalPlusUnit_quasiIso (twoChartLine R) C)
  have : IsIso (U.app C) :=
    isIso_derivedProjectionUnit_pullback_bounded R K a b hl hu hf
  have : IsIso (U.app ((godementTotalPlus (twoChartLine R)).obj C)) :=
    godementTotalPlus_derivedPushforwardUnit_isIso (projection R) C
  have : IsIso (DerivedCategory.Plus.Q.map (F.map η) ≫
      U.app ((godementTotalPlus (twoChartLine R)).obj C)) := by
    have hn := U.naturality η
    change DerivedCategory.Plus.Q.map (F.map η) ≫
      U.app ((godementTotalPlus (twoChartLine R)).obj C) = _ at hn
    rw [hn]
    exact inferInstanceAs (IsIso (U.app C ≫
      (derivedPushforwardPlus (projection R)).map (DerivedCategory.Plus.Q.map η)))
  exact IsIso.of_isIso_comp_right _ (U.app ((godementTotalPlus (twoChartLine R)).obj C))

/-- The canonical original positive chain map is a genuine quasi-isomorphism on bounded bundles. -/
lemma positivePlusUnit_quasiIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i)) (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hf : ∀ i, IsFiniteLocallyFree (Spec R) (K.obj.X i)) :
    QuasiIso ((positivePlusUnit R).app K).hom := by
  have := isIso_projectionPullbackComplexUnit R K hf
  have := pushforward_augmentation_isIso R K a b hl hu hf
  have hQ : IsIso (DerivedCategory.Plus.Q.map ((positivePlusUnit R).app K)) := by
    rw [positivePlusUnit_app, CategoryTheory.Functor.map_comp]
    infer_instance
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (Spec R).Modules _).mp
  change IsIso ((DerivedCategory.Plus.ι (C := (Spec R).Modules)).map
    (DerivedCategory.Plus.Q.map ((positivePlusUnit R).app K)))
  infer_instance

/-- The functor retains the original complex, rather than a chosen strict model. -/
lemma strictTotal_obj (X : Scheme.{u}) (K : StrictPerfect X) :
    ((strictTotal X).obj K).obj = (godementTotal X).obj K.obj := rfl

/-- The positive value is the original direct image of the actual pullback total. -/
lemma positive_obj (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    ((positive R).obj K).obj =
      ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotal (twoChartLine R)).obj ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
          (projection R)).obj K.obj)) := rfl

/-- Original source chain maps remain the original pulled, totalized, and pushed chain maps. -/
lemma positive_map (R : CommRingCat.{u}) {K L : StrictPerfect (Spec R)} (f : K ⟶ L) :
    ((positive R).map f).hom =
      ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (twoChartLine R)).map ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
          (projection R)).map f.hom)) := rfl

/-- The actual totalized source retains each specified original strict lower bound. -/
lemma strictTotal_isStrictlyGE (X : Scheme.{u}) (K : StrictPerfect X) (a : ℤ)
    [K.obj.IsStrictlyGE a] : ((strictTotal X).obj K).obj.IsStrictlyGE a := by
  change ((godementTotal X).obj K.obj).IsStrictlyGE a
  exact godementTotal_isStrictlyGE K.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- Actual pullback, totalization, and direct image retain the specified source lower bound. -/
lemma positive_isStrictlyGE (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) (a : ℤ)
    [K.obj.IsStrictlyGE a] : ((positive R).obj K).obj.IsStrictlyGE a := by
  have hp : ((strictPullback (projection R)).obj K).obj.IsStrictlyGE a := by
    apply (CochainComplex.isStrictlyGE_iff _ a).mpr
    intro n hn
    exact (Scheme.Modules.pullback (projection R)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
  have ht : ((pullbackTotal R).obj K).obj.IsStrictlyGE a :=
    strictTotal_isStrictlyGE _ _ a
  exact FlasqueCoefficients.G0Raw_isStrictlyGE R ((pullbackTotal R).obj K) a

/-- The canonical chain unit lifted into the original lower-bounded perfect model. -/
def positiveUnit (R : CommRingCat.{u}) :
    strictToBoundedBelow (Spec R) ⟶ positive R ⋙ FlasqueBoundedBelow.inclusion (Spec R) where
  app K := ObjectProperty.homMk
    (((positivePlusUnit R).app ((strictToPlus (Spec R)).obj K)).hom)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact congrArg (fun g => g.hom)
      ((positivePlusUnit R).naturality ((strictToPlus (Spec R)).map f))

/-- The lifted unit has exactly the original geometric-unit/augmentation chain component. -/
lemma positiveUnit_app (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    ((positiveUnit R).app K).hom =
      (projectionPullbackComplexUnit R ((strictToPlus (Spec R)).obj K)).hom ≫
        ((Scheme.Modules.pushforward (projection R)).mapHomologicalComplex (.up ℤ)).map
          ((godementTotalUnit (twoChartLine R)).app
            ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (projection R)).obj K.obj)) := rfl

/-- Every actual strict-source canonical unit is an original quasi-isomorphism. -/
lemma positiveUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (Spec R)).weq ((positiveUnit R).app K) := by
  obtain ⟨a, b, hb⟩ := K.property.1
  exact positivePlusUnit_quasiIso R ((strictToPlus (Spec R)).obj K) a b
    (fun i hi => hb i (Or.inl hi)) (fun i hi => hb i (Or.inr hi)) K.property.2

/-- The common target is the actual base Godement totalization of the positive value. -/
def spanMiddle (R : CommRingCat.{u}) :
    StrictPerfect (Spec R) ⥤ FlasqueBoundedBelow.Obj (Spec R) :=
  positive R ⋙ FlasqueBoundedBelow.inclusion (Spec R) ⋙ FlasqueBoundedBelow.total (Spec R)

lemma spanMiddle_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (spanMiddle R) :=
  (positive_exact R).comp
    ((FlasqueBoundedBelow.inclusion_exact (Spec R)).comp
      (FlasqueBoundedBelow.total_exact (Spec R)))

/-- Left leg: apply the actual base totalization to the original canonical positive unit. -/
def sourceUnitSpan (R : CommRingCat.{u}) : strictTotal (Spec R) ⟶ spanMiddle R :=
  CategoryTheory.Functor.whiskerRight (positiveUnit R) (FlasqueBoundedBelow.total (Spec R)) ≫
    (CategoryTheory.Functor.associator (positive R) (FlasqueBoundedBelow.inclusion (Spec R))
      (FlasqueBoundedBelow.total (Spec R))).hom

/-- The left span component is literally the base total of the original canonical unit. -/
lemma sourceUnitSpan_app (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (sourceUnitSpan R).app K =
      (FlasqueBoundedBelow.total (Spec R)).map ((positiveUnit R).app K) := by
  exact Category.comp_id _

lemma sourceUnitSpan_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((sourceUnitSpan R).app K) := by
  rw [sourceUnitSpan_app]
  exact FlasqueBoundedBelow.total_weak ((positiveUnit R).app K) (positiveUnit_weak R K)

/-- Right leg: the literal base augmentation of the original flasque positive value. -/
def positiveUnitSpan (R : CommRingCat.{u}) : positive R ⟶ spanMiddle R :=
  CategoryTheory.Functor.whiskerLeft (positive R) (FlasqueBoundedBelow.flasqueUnit (Spec R))

/-- The right span component is the literal native flasque-source augmentation. -/
lemma positiveUnitSpan_app (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (positiveUnitSpan R).app K =
      (FlasqueBoundedBelow.flasqueUnit (Spec R)).app ((positive R).obj K) := rfl

lemma positiveUnitSpan_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((positiveUnitSpan R).app K) :=
  FlasqueBoundedBelow.flasqueUnit_weak (Spec R) ((positive R).obj K)

/-- The natural weak span identifies the two original chosen-zero K-maps in every degree. -/
theorem positive_KMap_eq_strictTotal (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (positive_exact R) n = Waldhausen.KMap (strictTotal_exact (Spec R)) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (positive_exact R) (spanMiddle_exact R)
    (positiveUnitSpan R) (positiveUnitSpan_weak R) n).trans
      (Waldhausen.KMap_eq_of_weakNatTrans (strictTotal_exact (Spec R)) (spanMiddle_exact R)
        (sourceUnitSpan R) (sourceUnitSpan_weak R) n).symm

/-- The original composite of G0 and actual pulled total has the same source K-map. -/
theorem G0_comp_pullbackTotal_KMap (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (FlasqueCoefficients.G0_exact R) n).comp
      (Waldhausen.KMap (pullbackTotal_exact R) n) =
        Waldhausen.KMap (strictTotal_exact (Spec R)) n :=
  (Waldhausen.KMap_comp_KMap (pullbackTotal_exact R) (FlasqueCoefficients.G0_exact R) n).trans
    (positive_KMap_eq_strictTotal R n)

end Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
