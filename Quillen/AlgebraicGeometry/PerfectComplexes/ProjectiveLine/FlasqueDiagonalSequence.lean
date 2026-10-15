/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalExact
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Quillen.Waldhausen.ExtensionCategory.Structure

/-!
# The literal original diagonal conflation on the flasque model

The functorial original tensor incidence sequence is totalized and pushed along
the actual second projection. Its original maps give a genuine inherited
conflation, a Waldhausen cofibration sequence and an exact Reedy extension functor.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

/-- The literal original incidence natural transformation on underlying raw complexes. -/
def rawIncidence (R : CommRingCat.{u}) : raw R .first ⟶ raw R .second :=
  Functor.whiskerLeft (FlasqueBoundedBelow.objects (twoChartLine R)).ι
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalIncidence R))
        (.up ℤ))
      (godementTotal (relativeSquare R) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)))

/-- The literal original quotient natural transformation on underlying raw complexes. -/
def rawQuotient (R : CommRingCat.{u}) : raw R .second ⟶ raw R .third :=
  Functor.whiskerLeft (FlasqueBoundedBelow.objects (twoChartLine R)).ι
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalQuotientMap R))
        (.up ℤ))
      (godementTotal (relativeSquare R) ⋙
        (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)))

/-- Lift an original raw transformation by forgetting no map data. -/
def modelNatTrans (R : CommRingCat.{u}) {v w : Vertex} (a : raw R v ⟶ raw R w) :
    E R v ⟶ E R w where
  app K := ObjectProperty.homMk (a.app K)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact a.naturality f

/-- The original incidence after literal total and ordinary second image, with original maps. -/
def incidence (R : CommRingCat.{u}) : E R .first ⟶ E R .second :=
  modelNatTrans R (rawIncidence R)

/-- The original adjoint quotient after literal total and ordinary second image. -/
def quotient (R : CommRingCat.{u}) : E R .second ⟶ E R .third :=
  modelNatTrans R (rawQuotient R)

/-- The exact original coefficient arrows retain their accepted sheaf zero composite. -/
lemma coefficientIncidence_quotient (R : CommRingCat.{u}) :
    diagonalCoefficientMap R (diagonalIncidence R) ≫
      diagonalCoefficientMap R (diagonalQuotientMap R) = 0 := by
  apply NatTrans.ext
  funext M
  exact (diagonalBundleTensorSequence R M).zero

/-- Termwise mapping retains an actual zero composite of natural transformations. -/
lemma mapComplexNatTrans_zero {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    NatTrans.mapHomologicalComplex a (.up ℤ) ≫
      NatTrans.mapHomologicalComplex b (.up ℤ) = 0 := by
  rw [← NatTrans.mapHomologicalComplex_comp, h]
  apply NatTrans.ext
  funext K
  ext n : 1
  rfl

/-- Whiskering by an actual additive functor retains an actual zero composite. -/
lemma whiskeredNatTrans_zero {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Preadditive C] [Preadditive D] (I : A ⥤ B) {F G H : B ⥤ C}
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (T : C ⥤ D) [T.Additive] :
    Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0 := by
  apply NatTrans.ext
  funext K
  change T.map (a.app (I.obj K)) ≫ T.map (b.app (I.obj K)) = 0
  have hz : a.app (I.obj K) ≫ b.app (I.obj K) = 0 := NatTrans.congr_app h (I.obj K)
  rw [← T.map_comp, hz, T.map_zero]

/-- Two actual natural maps with zero composite retain their actual pointwise short complexes. -/
def naturalSequence {A B : Type*} [Category A] [Category B] [Preadditive B]
    {F G H : A ⥤ B} (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    A ⥤ ShortComplex B where
  obj K := ShortComplex.mk (a.app K) (b.app K) (NatTrans.congr_app h K)
  map f := ShortComplex.homMk (F.map f) (G.map f) (H.map f) (a.naturality f) (b.naturality f)
  map_id K := by
    apply ShortComplex.hom_ext
    · exact F.map_id K
    · exact G.map_id K
    · exact H.map_id K
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact F.map_comp f g
    · exact G.map_comp f g
    · exact H.map_comp f g

/-- Source restriction retains a pointwise zero composite. -/
lemma whiskerLeftNatTrans_zero {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive C] (I : A ⥤ B) {F G H : B ⥤ C}
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0 := by
  apply NatTrans.ext
  funext K
  exact NatTrans.congr_app h (I.obj K)

/-- The mapped sequence equation is checked abstractly before expanding the actual total. -/
lemma naturalSequence_whiskered_map {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] [Preadditive C] [Preadditive D]
    (I : A ⥤ B) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H)
    (T : C ⥤ D) [T.Additive]
    (h₁ : Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0)
    (h₂ : Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0) (K : A) :
    (naturalSequence (Functor.whiskerLeft I (Functor.whiskerRight a T))
      (Functor.whiskerLeft I (Functor.whiskerRight b T)) h₂).obj K =
      (((naturalSequence (Functor.whiskerLeft I a) (Functor.whiskerLeft I b) h₁).obj K).map
        T) := rfl

/-- Exactness transfers to the same literal whiskered maps before expanding the actual total. -/
lemma naturalSequence_whiskered_shortExact {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] [Abelian C] [Abelian D]
    (I : A ⥤ B) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H)
    (T : C ⥤ D) [T.Additive]
    (h₁ : Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0)
    (h₂ : Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0) (K : A)
    (hS : (((naturalSequence (Functor.whiskerLeft I a)
      (Functor.whiskerLeft I b) h₁).obj K).map T).ShortExact) :
    ((naturalSequence (Functor.whiskerLeft I (Functor.whiskerRight a T))
      (Functor.whiskerLeft I (Functor.whiskerRight b T)) h₂).obj K).ShortExact := by
  rw [naturalSequence_whiskered_map]
  exact hS

/-- The literal original coefficient sequence, retaining all original chain differentials. -/
def coefficientSequenceFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ ShortComplex (Complex (relativeSquare R)) :=
  naturalSequence
    (Functor.whiskerLeft (FlasqueBoundedBelow.objects (twoChartLine R)).ι
      (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalIncidence R)) (.up ℤ)))
    (Functor.whiskerLeft (FlasqueBoundedBelow.objects (twoChartLine R)).ι
      (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalQuotientMap R)) (.up ℤ)))
    (whiskerLeftNatTrans_zero _ _ _
      (mapComplexNatTrans_zero _ _ (coefficientIncidence_quotient R)))

/-- This direct encoding is the actual existing original bounded-below coefficient sequence. -/
lemma coefficientSequence_original (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (coefficientSequenceFunctor R).obj K =
      ((diagonalComplexSequenceFunctor R).obj
        ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)).map
          (CochainComplex.Plus.ι (relativeSquare R).Modules) := rfl

/-- Exactness concerns the literal original sequence on all coefficient terms. -/
lemma coefficientSequence_shortExact (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((coefficientSequenceFunctor R).obj K).ShortExact := by
  rw [coefficientSequence_original]
  exact diagonalComplexSequence_shortExact R
    ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)

/-- The raw original maps retain the accepted tensor-incidence zero composite. -/
lemma rawIncidence_quotient (R : CommRingCat.{u}) : rawIncidence R ≫ rawQuotient R = 0 :=
  whiskeredNatTrans_zero (FlasqueBoundedBelow.objects (twoChartLine R)).ι
    (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalIncidence R)) (.up ℤ))
    (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalQuotientMap R)) (.up ℤ))
    (mapComplexNatTrans_zero _ _ (coefficientIncidence_quotient R))
    (godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))

/-- The original raw sequence is expressed by its actual original natural maps. -/
def rawSequenceFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ ShortComplex (Complex (twoChartLine R)) :=
  naturalSequence (rawIncidence R) (rawQuotient R) (rawIncidence_quotient R)

/-- Actual all-coefficient exactness, literal total exactness and the original flasque kernel. -/
lemma rawSequence_shortExact (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((rawSequenceFunctor R).obj K).ShortExact := by
  apply naturalSequence_whiskered_shortExact
    (FlasqueBoundedBelow.objects (twoChartLine R)).ι
    (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalIncidence R)) (.up ℤ))
    (NatTrans.mapHomologicalComplex (diagonalCoefficientMap R (diagonalQuotientMap R)) (.up ℤ))
    (godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))
    (whiskerLeftNatTrans_zero _ _ _
      (mapComplexNatTrans_zero _ _ (coefficientIncidence_quotient R)))
    (rawIncidence_quotient R) K
  simp only [ShortComplex.map_comp]
  exact pushforwardComplex_shortExact_of_flasque_kernel (relativeSecond R)
    (godementTotal_shortExact (coefficientSequence_shortExact R K))
    (totalCoefficient_flasque R .first K)

/-- Lift a literal sequence using the supplied membership proofs without changing any maps. -/
def liftedSequence {A B : Type*} [Category A] [Category B] [Preadditive B]
    (P : ObjectProperty B) {F G H : A ⥤ B}
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (hH : ∀ K, P (H.obj K))
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (K : A) :
    ShortComplex P.FullSubcategory :=
  { X₁ := (P.lift F hF).obj K
    X₂ := (P.lift G hG).obj K
    X₃ := (P.lift H hH).obj K
    f := ObjectProperty.homMk (a.app K)
    g := ObjectProperty.homMk (b.app K)
    zero := ObjectProperty.hom_ext _ (NatTrans.congr_app h K) }

/-- Forgetting a lifted literal sequence recovers the entire original sequence. -/
lemma liftedSequence_underlying {A B : Type*} [Category A] [Category B] [Preadditive B]
    (P : ObjectProperty B) {F G H : A ⥤ B}
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (hH : ∀ K, P (H.obj K))
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (K : A) :
    (liftedSequence P hF hG hH a b h K).map P.ι = (naturalSequence a b h).obj K := rfl

/-- The original incidence/quotient composite remains literally zero. -/
lemma incidence_quotient (R : CommRingCat.{u}) : incidence R ≫ quotient R = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app (rawIncidence_quotient R) K

/-- The genuine functorial original model sequence with every original map retained. -/
def sequenceFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
      ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)) where
  obj K := liftedSequence (FlasqueBoundedBelow.objects (twoChartLine R))
    (raw_objects R .first) (raw_objects R .second) (raw_objects R .third)
    (rawIncidence R) (rawQuotient R) (rawIncidence_quotient R) K
  map f := ShortComplex.homMk ((E R .first).map f) ((E R .second).map f)
    ((E R .third).map f) ((incidence R).naturality f) ((quotient R).naturality f)
  map_id K := by
    apply ShortComplex.hom_ext
    · exact (E R .first).map_id K
    · exact (E R .second).map_id K
    · exact (E R .third).map_id K
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact (E R .first).map_comp f g
    · exact (E R .second).map_comp f g
    · exact (E R .third).map_comp f g

/-- Forgetting the model predicates recovers the actual original pushed total sequence. -/
lemma sequence_underlying (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((sequenceFunctor R).obj K).map (FlasqueBoundedBelow.objects (twoChartLine R)).ι =
      (rawSequenceFunctor R).obj K :=
  liftedSequence_underlying (FlasqueBoundedBelow.objects (twoChartLine R))
    (raw_objects R .first) (raw_objects R .second) (raw_objects R .third)
    (rawIncidence R) (rawQuotient R) (rawIncidence_quotient R) K

/-- The original short exact sequence is an actual conflation of the inherited exact structure. -/
lemma sequence_conflation (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (modelExactStructure R).conflation ((sequenceFunctor R).obj K) := by
  change (((sequenceFunctor R).obj K).map
    (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact
  rw [sequence_underlying]
  exact rawSequence_shortExact R K

/-- The actual incidence is a quotient-bearing cofibration in the original flasque model. -/
lemma incidence_cof (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof ((incidence R).app K) :=
  (modelExactStructure R).inflation_of_conflation (sequence_conflation R K)

/-- The relative quotient criterion applies to any actual Waldhausen structures
whose cofibrations are the stated exact inflations; weak arrows need not be isomorphisms. -/
lemma cofibrationTransformation_of_conflations {C D : Type*}
    [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (EC : ExactStructure C) (ED : ExactStructure D)
    (V : Waldhausen.Structure C) (W : Waldhausen.Structure D)
    (hV : V.cof = EC.inflation) (hW : W.cof = ED.inflation)
    {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0)
    (hc : ∀ K, ED.conflation ((naturalSequence a b h).obj K))
    (hH : ∀ {K L} (f : K ⟶ L), EC.inflation f → ED.inflation (H.map f)) :
    Waldhausen.Additivity.IsCofibrationTransformation W a V := by
  have ha : ∀ K, W.cof (a.app K) := by
    intro K
    rw [hW]
    exact ED.inflation_of_conflation (hc K)
  refine ⟨ha, ?_⟩
  intro K L f hf
  let : HasPushout (a.app K) (F.map f) :=
    Waldhausen.Additivity.hasPushout W a ha f
  let : HasPushout ((naturalSequence a b h).obj K).f ((naturalSequence a b h).map f).τ₁ :=
    (inferInstance : HasPushout (a.app K) (F.map f))
  have hi := Waldhausen.GilletWaldhausen.relativePushout_inflation ED
    ((naturalSequence a b h).map f) (hc K) (hc L) (hH f (hV ▸ hf))
  change W.cof (pushout.desc (G.map f) (a.app L) (a.naturality f).symm)
  rw [hW]
  exact hi

/-- Original exact quotient functor forces the genuine relative-cofibration condition. -/
lemma incidence_cofibration (R : CommRingCat.{u}) :
    Waldhausen.Additivity.IsCofibrationTransformation
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (incidence R)
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) :=
  cofibrationTransformation_of_conflations (modelExactStructure R) (modelExactStructure R)
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)) rfl rfl
    (incidence R) (quotient R) (incidence_quotient R)
    (fun K => sequence_conflation R K)
    (fun f hf => (EExactFunctor R .third).map_inflation f hf)

/-- The literal original sequence meets all structural Waldhausen additivity hypotheses. -/
lemma sequence_isCofibrationSequence (R : CommRingCat.{u}) :
    Waldhausen.Additivity.IsCofibrationSequence
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (incidence R) (quotient R) where
  exactF := E_exact R .first
  exactG := E_exact R .second
  exactH := E_exact R .third
  cofibration := incidence_cofibration R
  cofiber K := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _
    ((modelExactStructure R).cokernel _ (sequence_conflation R K))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).isZero _ _

/-- Any actual cofibration transformation retains its actual incidence arrows in the extension. -/
def naturalExtension {C D : Type*} [Category C] [Category D]
    (W : Waldhausen.Structure D) {F G : C ⥤ D} (a : F ⟶ G)
    (ha : ∀ K, W.cof (a.app K)) : C ⥤ Waldhausen.ExtensionCategory.Obj W where
  obj K := ⟨Arrow.mk (a.app K), ha K⟩
  map f := ObjectProperty.homMk
    (Arrow.homMk (F.map f) (G.map f) (a.naturality f))
  map_id K := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact F.map_id K
    · exact G.map_id K
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact F.map_comp f g
    · exact G.map_comp f g

/-- Relative cofibrations and exact endpoint functors give the actual Reedy exact functor. -/
lemma naturalExtension_exact {C D : Type*} [Category C] [Category D]
    (V : Waldhausen.Structure C) (W : Waldhausen.Structure D)
    {F G : C ⥤ D} (a : F ⟶ G)
    (ha : Waldhausen.Additivity.IsCofibrationTransformation W a V)
    (hF : Waldhausen.IsExact V.cof V.weq W.cof W.weq F)
    (hG : Waldhausen.IsExact V.cof V.weq W.cof W.weq G) :
    Waldhausen.IsExact V.cof V.weq (Waldhausen.ExtensionCategory.waldhausenStructure W).cof
      (Waldhausen.ExtensionCategory.waldhausenStructure W).weq
      (naturalExtension W a ha.app_cof) where
  zero h := Waldhausen.ExtensionCategory.isZero_of_components _ _ (hF.zero h) (hG.zero h)
  cofibration f hf := by
    apply Waldhausen.ExtensionCategory.cof_of_relative W ((naturalExtension W a ha.app_cof).map f)
      (hF.cofibration f hf)
      (Waldhausen.Additivity.pushoutFunctor_isPushout W a ha.app_cof (Arrow.mk f))
      (Waldhausen.Additivity.comparison W a ha.app_cof (Arrow.mk f))
    · exact Waldhausen.Additivity.sourceι_comparison W a ha.app_cof (Arrow.mk f)
    · exact Waldhausen.Additivity.targetι_comparison W a ha.app_cof (Arrow.mk f)
    · exact ha.relative_cof f hf
  weak f hf := ⟨hF.weak f hf, hG.weak f hf⟩
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (Waldhausen.ExtensionCategory.forget W)
    exact Waldhausen.ExtensionCategory.arrow_isPushout _ _ _ _
      (hF.pushout hi h) (hG.pushout hi h)

/-- Literal original incidence arrows form an actual functor into the extension category. -/
def extensionFunctor (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
      Waldhausen.ExtensionCategory.Obj (FlasqueBoundedBelow.waldhausen (twoChartLine R)) :=
  naturalExtension (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (incidence R) (incidence_cof R)

/-- The original exact first/second functors and quotient criterion prove Reedy exactness. -/
lemma extension_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (Waldhausen.ExtensionCategory.waldhausenStructure
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))).cof
    (Waldhausen.ExtensionCategory.waldhausenStructure
      (FlasqueBoundedBelow.waldhausen (twoChartLine R))).weq (extensionFunctor R) :=
  naturalExtension_exact (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)) (incidence R)
    (incidence_cofibration R) (E_exact R .first) (E_exact R .second)

/-- The extension source is exactly the original first vertex functor. -/
lemma extension_source (R : CommRingCat.{u}) :
    extensionFunctor R ⋙ Waldhausen.ExtensionCategory.source
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) = E R .first := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The extension middle is exactly the original second vertex functor. -/
lemma extension_middle (R : CommRingCat.{u}) :
    extensionFunctor R ⋙ Waldhausen.ExtensionCategory.middle
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)) = E R .second := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
