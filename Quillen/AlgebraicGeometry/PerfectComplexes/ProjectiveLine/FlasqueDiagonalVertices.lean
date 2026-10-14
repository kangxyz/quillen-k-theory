/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.OriginalPerfectGeneration

/-!
# Literal flasque diagonal vertices

Each vertex is the ordinary second image of the Godement total of the original
first-pullback/right-tensor coefficient complex. Perfection is transferred
through the actual total derived comparison and the accepted P3 endpoint maps.
No arbitrary-base perfect-pushforward theorem or chosen coefficient model is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
open FlasqueCoefficients

local instance standardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The three original incidence-sequence vertices, in their original order. -/
inductive Vertex
  | first | second | third

/-- The literal original sheaf at the selected incidence-sequence vertex. -/
def vertexSheaf (R : CommRingCat.{u}) : Vertex → (relativeSquare R).Modules
  | .first => (diagonalIncidenceSequence R).X₁
  | .second => (diagonalIncidenceSequence R).X₂
  | .third => (diagonalIncidenceSequence R).X₃

/-- Original coefficient pullback/right tensor, with every original differential retained. -/
abbrev coefficient (R : CommRingCat.{u}) (v : Vertex) :=
  diagonalCoefficientFunctor R (vertexSheaf R v)

instance coefficient_preservesHomology (R : CommRingCat.{u}) (v : Vertex) :
    (coefficient R v).PreservesHomology := by
  cases v <;> dsimp [coefficient, vertexSheaf] <;> infer_instance

/-- Original coefficient, then literal total, then ordinary second image, in D+ complexes. -/
def rawPlus (R : CommRingCat.{u}) (v : Vertex) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  toPlus (twoChartLine R) ⋙ (coefficient R v).mapCochainComplexPlus ⋙
    godementTotalPlus (relativeSquare R) ⋙
    (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus

/-- The actual original chain complex p2_* T_Z(F_v(K)), with no outer total. -/
def raw (R : CommRingCat.{u}) (v : Vertex) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    (coefficient R v).mapHomologicalComplex (.up ℤ) ⋙ godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)

instance raw_additive (R : CommRingCat.{u}) (v : Vertex) : (raw R v).Additive := by
  dsimp [raw]
  infer_instance

/-- Original exact coefficient mapping preserves every specified strict lower bound. -/
lemma coefficient_isStrictlyGE (R : CommRingCat.{u}) (v : Vertex)
    (K : Complex (twoChartLine R)) (a : ℤ) [K.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE
      (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K) a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (coefficient R v).map_isZero (CochainComplex.isZero_of_isStrictlyGE K a n hn)

/-- Literal total and ordinary second image retain the input's specified lower bound. -/
lemma raw_isStrictlyGE (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((raw R v).obj K).IsStrictlyGE a := by
  let C : Complex (relativeSquare R) :=
    ((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj
  let : C.IsStrictlyGE a := coefficient_isStrictlyGE R v K.obj a
  let : ((godementTotal (relativeSquare R)).obj C).IsStrictlyGE a :=
    godementTotal_isStrictlyGE C a
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE C a n hn)
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (relativeSecond R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE ((godementTotal (relativeSquare R)).obj C) a n hn)

/-- Every actual totalized original coefficient has flasque terms. -/
lemma totalCoefficient_flasque (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((godementTotal (relativeSquare R)).obj
        (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj)).X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  let C : Complex (relativeSquare R) :=
    ((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj
  let : C.IsStrictlyGE a := coefficient_isStrictlyGE R v K.obj a
  exact godementTotal_isFlasque C a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE C a i hi) n

/-- Ordinary second image of each literal total has flasque terms. -/
lemma raw_flasque (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((raw R v).obj K).X n).presheaf := by
  let : TopCat.Presheaf.IsFlasque
      (((godementTotal (relativeSquare R)).obj
        (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj)).X n).presheaf :=
    totalCoefficient_flasque R v K n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (relativeSecond R)).obj
      (((godementTotal (relativeSquare R)).obj
        (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj)).X n)).presheaf
  infer_instance

/-- The actual installed unit and total augmentation compare each original raw vertex naturally. -/
def rawDerivedIso (R : CommRingCat.{u}) (v : Vertex) :
    rawPlus R v ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ (coefficient R v).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (relativeSecond R) :=
  Functor.associator (toPlus (twoChartLine R))
    ((coefficient R v).mapCochainComplexPlus ⋙ godementTotalPlus (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus)
    DerivedCategory.Plus.Q ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.associator (coefficient R v).mapCochainComplexPlus
        (godementTotalPlus (relativeSquare R) ⋙
          (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus)
        DerivedCategory.Plus.Q ≪≫
      Functor.isoWhiskerLeft (coefficient R v).mapCochainComplexPlus
        (Functor.associator (godementTotalPlus (relativeSquare R))
          (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
          DerivedCategory.Plus.Q ≪≫ godementTotalDerivedPushforwardIso (relativeSecond R)))

/-- Literal first raw vertex to the accepted original projected first vertex. -/
def rawProjectedFirstIso (R : CommRingCat.{u}) :
    rawPlus R .first ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        diagonalDerivedComplexProjectedTriangleFunctor R ⋙
          CategoryTheory.Pretriangulated.Triangle.π₁ :=
  rawDerivedIso R .first ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight (diagonalComplexFirstFunctorIso R).symm
        (derivedPushforwardPlus (relativeSecond R))) ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (diagonalDerivedComplexTriangleFactors R)
          CategoryTheory.Pretriangulated.Triangle.π₁).symm
        (derivedPushforwardPlus (relativeSecond R)))

/-- Literal second raw vertex to the accepted original projected second vertex. -/
def rawProjectedSecondIso (R : CommRingCat.{u}) :
    rawPlus R .second ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        diagonalDerivedComplexProjectedTriangleFunctor R ⋙
          CategoryTheory.Pretriangulated.Triangle.π₂ :=
  rawDerivedIso R .second ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight (diagonalComplexSecondFunctorIso R).symm
        (derivedPushforwardPlus (relativeSecond R))) ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (diagonalDerivedComplexTriangleFactors R)
          CategoryTheory.Pretriangulated.Triangle.π₂).symm
        (derivedPushforwardPlus (relativeSecond R)))

/-- The third raw vertex retains the original closed projection and actual section comparison. -/
def rawProjectedThirdIso (R : CommRingCat.{u}) :
    rawPlus R .third ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        diagonalDerivedComplexProjectedTriangleFunctor R ⋙
          CategoryTheory.Pretriangulated.Triangle.π₃ :=
  rawDerivedIso R .third ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight (diagonalComplexThirdFunctorIso R).symm
        (derivedPushforwardPlus (relativeSecond R))) ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R))
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (diagonalDerivedComplexTriangleFactors R)
          CategoryTheory.Pretriangulated.Triangle.π₃).symm
        (derivedPushforwardPlus (relativeSecond R)))

/-- Intrinsic perfect input, localized without choosing a representative or changing its maps. -/
def toOriginalPerfectPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ OriginalPerfectPlus R :=
  ObjectProperty.lift _ (toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q)
    (fun K => (perfectDerivedObjects_toDerived_iff (twoChartLine R) K.obj).mpr K.property.1.1)

/-- Exact sheaf functors that preserve actual local perfection preserve intrinsic perfect D+. -/
lemma perfect_exactDerived {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] [F.PreservesHomology]
    (hF : ∀ K : Complex X, locallyPerfect X K →
      locallyPerfect Y ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (K : DerivedCategory.Plus X.Modules)
    (hK : perfectDerivedObjects X (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects Y (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj K)) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let := Localization.essSurj DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
  let P := DerivedCategory.Plus.Q.objPreimage K
  let eP := DerivedCategory.Plus.Q.objObjPreimageIso K
  have hP : locallyPerfect X P.obj :=
    (perfectDerivedObjects_toDerived_iff X P.obj).mp
      ((perfectDerivedObjects X).prop_of_iso (DerivedCategory.Plus.ι.mapIso eP.symm) hK)
  let e : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj P) ≅
      F.rightDerivedFunctorPlus.obj K :=
    asIso (F.rightDerivedFunctorPlusUnit.app P) ≪≫ F.rightDerivedFunctorPlus.mapIso eP
  exact (perfectDerivedObjects Y).prop_of_iso (DerivedCategory.Plus.ι.mapIso e)
    ((perfectDerivedObjects_toDerived_iff Y _).mpr (hF P.obj hP))

/-- Exact original quotient-line tensors preserve actual local perfection. -/
lemma quotientLeft_locallyPerfect (R : CommRingCat.{u})
    (K : Complex (twoChartLine R)) (hK : locallyPerfect (twoChartLine R) K) :
    locallyPerfect (twoChartLine R)
      ((tensorByLineComplex (tautologicalQuotientLine R)).obj K) := by
  let e : ∀ b : Bool, (tautologicalQuotientLine R).restrict (polynomialChart R b) ≅
      SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf := by
    intro b
    cases b
    · exact tautologicalQuotientMinusIso R
    · exact tautologicalQuotientPlusIso R
  exact locallyPerfect_tensorByLine (tautologicalQuotientLine R)
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R)
    (polynomialChart_cover R) e hK

/-- The three accepted intended P3 endpoints are intrinsically perfect at every actual input. -/
lemma endpoint_perfect (R : CommRingCat.{u}) (v : Vertex)
    (K : OriginalPerfectPlus R) :
    perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj
      (match v with
      | .first => (diagonalPerfectGenerationFirstFunctor R).obj K.obj
      | .second => (diagonalPerfectGenerationSecondFunctor R).obj K.obj
      | .third => ((moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus).obj K.obj)) := by
  have hp : ∀ A : DerivedCategory.Plus (Spec R).Modules,
      perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj A) →
        perfectDerivedObjects (twoChartLine R)
          (DerivedCategory.Plus.ι.obj ((derivedFlatPullbackPlus (projection R)).obj A)) := by
    intro A hA
    exact perfect_exactDerived (Scheme.Modules.pullback (projection R))
      (fun _ h => locallyPerfect_flatPullback (projection R) h) A hA
  cases v
  · exact hp _ (perfect_derivedProjection_of_perfect R _
      (perfect_derivedTautologicalRightTensor R K.obj K.property))
  · exact perfect_exactDerived
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (quotientLeft_locallyPerfect R) _ (hp _ (perfect_diagonalGenerationG0 R K))
  · exact perfect_exactDerived
      (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (fun C hC => locallyPerfect_of_iso
        ((tensorByLineComplexSymmetry (tautologicalQuotientLine R)).app C)
        (quotientLeft_locallyPerfect R C hC)) K.obj K.property

/-- The first original raw complex has the specified natural intended endpoint iso. -/
def firstEndpointIso (R : CommRingCat.{u}) :
    rawPlus R .first ⋙ DerivedCategory.Plus.Q ≅
      toOriginalPerfectPlus R ⋙ originalPerfectPlusInclusion R ⋙
        diagonalPerfectGenerationFirstFunctor R :=
  rawProjectedFirstIso R ≪≫
    Functor.isoWhiskerLeft (toOriginalPerfectPlus R) (diagonalPerfectGenerationFirstIso R).symm

/-- The second original raw complex has the specified natural intended endpoint iso. -/
def secondEndpointIso (R : CommRingCat.{u}) :
    rawPlus R .second ⋙ DerivedCategory.Plus.Q ≅
      toOriginalPerfectPlus R ⋙ originalPerfectPlusInclusion R ⋙
        diagonalPerfectGenerationSecondFunctor R :=
  rawProjectedSecondIso R ≪≫
    Functor.isoWhiskerLeft (toOriginalPerfectPlus R) (diagonalPerfectGenerationSecondIso R).symm

/-- The third original raw complex retains the original right-Q/closed/section iso. -/
def thirdEndpointIso (R : CommRingCat.{u}) :
    rawPlus R .third ⋙ DerivedCategory.Plus.Q ≅
      toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus :=
  rawProjectedThirdIso R ≪≫
    Functor.isoWhiskerLeft (toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q)
      (diagonalDerivedComplexProjectedVertexIso R)

/-- Perfection transfers to the actual ordinary p2_* total values through the original P3 isos. -/
lemma raw_locallyPerfect (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((raw R v).obj K) := by
  apply (perfectDerivedObjects_toDerived_iff (twoChartLine R) ((raw R v).obj K)).mp
  have h := endpoint_perfect R v ((toOriginalPerfectPlus R).obj K)
  cases v
  · exact (perfectDerivedObjects (twoChartLine R)).prop_of_iso
      (DerivedCategory.Plus.ι.mapIso ((firstEndpointIso R).app K).symm) h
  · exact (perfectDerivedObjects (twoChartLine R)).prop_of_iso
      (DerivedCategory.Plus.ι.mapIso ((secondEndpointIso R).app K).symm) h
  · exact (perfectDerivedObjects (twoChartLine R)).prop_of_iso
      (DerivedCategory.Plus.ι.mapIso ((thirdEndpointIso R).app K).symm) h

/-- Each actual original vertex belongs to the full flasque-perfect target category. -/
lemma raw_objects (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (twoChartLine R) ((raw R v).obj K) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨⟨raw_locallyPerfect R v K, a, raw_isStrictlyGE R v K a⟩, raw_flasque R v K⟩

/-- The three literal original model endofunctors E_v(K)=p2_* T_Z(F_v(K)). -/
def E (R : CommRingCat.{u}) (v : Vertex) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (raw R v) (raw_objects R v)

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
