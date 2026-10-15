/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueThirdTensor

/-! # Actual original third endpoint span in the flasque perfect model -/

@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint

local instance diagonalClosed (R : CommRingCat.{u}) :
    IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R

/-- Forget only proofs after the original right-Q tensor. -/
def rightQPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  FlasqueCoefficients.toPlus (twoChartLine R) ⋙ (quotientTensor R).mapCochainComplexPlus

/-- The actual source total on the actual original right-Q complex. -/
def sourceTotalPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  rightQPlus R ⋙ godementTotalPlus (twoChartLine R)

/-- The ordinary second image of the product total of the original section image. -/
def sectionPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  rightQPlus R ⋙ sectionTotalImage (relativeDiagonal R) (relativeSecond R)

/-- The common vertex includes the source total before the original closed section. -/
def centerPlus (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex.Plus (twoChartLine R).Modules :=
  rightQPlus R ⋙ sectionRepeatedTotalImage (relativeDiagonal R) (relativeSecond R)

/-- Original third coefficient projection formula, its literal complex lift and associators. -/
def thirdSectionPlusIso (R : CommRingCat.{u}) :
    FlasqueDiagonal.rawPlus R .third ≅ sectionPlus R := by
  let A := FlasqueCoefficients.toPlus (twoChartLine R)
  let B := (quotientTensor R).mapCochainComplexPlus
  let D := (Scheme.Modules.pushforward (relativeDiagonal R)).mapCochainComplexPlus
  let V := godementTotalPlus (relativeSquare R) ⋙
    (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
  let e : (FlasqueDiagonal.coefficient R .third).mapCochainComplexPlus ≅ B ⋙ D :=
    NatIso.mapCochainComplexPlus (diagonalCoefficientThirdIso R) ≪≫
      (quotientTensor R).mapCochainComplexPlusCompIso
        (Scheme.Modules.pushforward (relativeDiagonal R))
  exact isoWhiskerLeft A (isoWhiskerRight e V ≪≫ associator B D V) ≪≫
    (associator A B (D ⋙ V)).symm

/-- The original third coefficient map, followed by the actual section/source augmentation. -/
def thirdToCenterPlus (R : CommRingCat.{u}) :
    FlasqueDiagonal.rawPlus R .third ⟶ centerPlus R :=
  (thirdSectionPlusIso R).hom ≫
    whiskerLeft (rightQPlus R) (sectionTotalToRepeated (relativeDiagonal R) (relativeSecond R))

/-- The exact inverse original geometric section iso followed by the pushed flasque unit. -/
def totalToCenterPlus (R : CommRingCat.{u}) : sourceTotalPlus R ⟶ centerPlus R :=
  whiskerLeft (rightQPlus R) (sectionSourceTotalToRepeated
    (relativeDiagonal R) (relativeSecond R) (relativeDiagonal_second R))

/-- The actual source total belongs to the original flasque perfect predicate. -/
lemma sourceTotal_objects (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (twoChartLine R) ((sourceTotalPlus R).obj K).obj := by
  change FlasqueBoundedBelow.objects (twoChartLine R)
    ((godementTotal (twoChartLine R)).obj ((rightQRaw R).obj K))
  exact FlasqueBoundedBelow.godement_objects (rightQ_objects R K)

/-- The prescribed second leg is weak before any perfect-model lifting. -/
lemma totalToCenterPlus_quasiIso (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((totalToCenterPlus R).app K).hom :=
  sectionSourceTotalToRepeated_quasiIso (relativeDiagonal R) (relativeSecond R)
    (relativeDiagonal_second R) ((rightQPlus R).obj K)

/-- The prescribed first leg is the original coefficient iso followed by a genuine weak arrow. -/
lemma thirdToCenterPlus_quasiIso (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((thirdToCenterPlus R).app K).hom := by
  let : QuasiIso ((sectionTotalToRepeated (relativeDiagonal R) (relativeSecond R)).app
      ((rightQPlus R).obj K)).hom :=
    sectionTotalToRepeated_quasiIso (relativeDiagonal R) (relativeSecond R)
      ((rightQPlus R).obj K)
  let : IsIso (((thirdSectionPlusIso R).hom.app K).hom) :=
    inferInstanceAs (IsIso ((CochainComplex.Plus.ι (twoChartLine R).Modules).map
      ((thirdSectionPlusIso R).hom.app K)))
  change QuasiIso (((thirdSectionPlusIso R).hom.app K).hom ≫
    ((sectionTotalToRepeated (relativeDiagonal R) (relativeSecond R)).app
      ((rightQPlus R).obj K)).hom)
  infer_instance

/-- The literal underlying common complex, retaining all original maps. -/
def centerRaw (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  centerPlus R ⋙ CochainComplex.Plus.ι (twoChartLine R).Modules

/-- The actual common complex is perfect by the actual quasi-isomorphism from T_P(K tensor Q). -/
lemma center_locallyPerfect (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((centerRaw R).obj K) := by
  let : QuasiIso ((totalToCenterPlus R).app K).hom := totalToCenterPlus_quasiIso R K
  exact (locallyPerfect_iff_of_quasiIso ((totalToCenterPlus R).app K).hom).mp
    (sourceTotal_objects R K).1.1

/-- The original section image before the product total has a genuine lower bound. -/
def centerInputPlus (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    CochainComplex.Plus (relativeSquare R).Modules :=
  (Scheme.Modules.pushforward (relativeDiagonal R)).mapCochainComplexPlus.obj
    ((sourceTotalPlus R).obj K)

/-- Product totalization and actual ordinary second image supply flasqueness of the center. -/
lemma center_flasque (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((centerRaw R).obj K).X n).presheaf := by
  let J := centerInputPlus R K
  obtain ⟨a, ha⟩ := J.property
  let := ha
  let : TopCat.Presheaf.IsFlasque
      (((godementTotal (relativeSquare R)).obj J.obj).X n).presheaf :=
    godementTotal_isFlasque J.obj a
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE J.obj a i hi) n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (relativeSecond R)).obj
      (((godementTotal (relativeSquare R)).obj J.obj).X n)).presheaf
  infer_instance

/-- The actual lower-bound proof, perfection and flasque terms define the model value. -/
lemma center_objects (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (twoChartLine R) ((centerRaw R).obj K) :=
  ⟨⟨center_locallyPerfect R K, ((centerPlus R).obj K).property⟩, center_flasque R K⟩

/-- The common vertex in the genuine original flasque-perfect category. -/
def center (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (centerRaw R) (center_objects R)

/-- The original E-third proof-forgetting comparison followed by the prescribed first leg. -/
def modelThirdToCenterPlus (R : CommRingCat.{u}) :
    FlasqueDiagonal.E R .third ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⟶ centerPlus R :=
  (FlasqueDiagonal.EPlusIso R .third).hom ≫ thirdToCenterPlus R

/-- The actual first natural arrow in the original flasque-perfect model. -/
def thirdToCenter (R : CommRingCat.{u}) : FlasqueDiagonal.E R .third ⟶ center R where
  app K := ObjectProperty.homMk ((modelThirdToCenterPlus R).app K).hom
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    have hn :=
      (CochainComplex.Plus.ι (twoChartLine R).Modules).congr_map
        ((modelThirdToCenterPlus R).naturality f)
    dsimp only [Functor.map_comp, Functor.comp_map, CochainComplex.Plus.ι,
      ObjectProperty.ι, inducedFunctor, FlasqueCoefficients.toPlus, ObjectProperty.lift,
      ObjectProperty.homMk, center, centerRaw] at hn ⊢
    exact hn

/-- The actual second natural arrow uses the original section inverse and flasque augmentation. -/
def totalToCenter (R : CommRingCat.{u}) : rightQTotal R ⟶ center R where
  app K := ObjectProperty.homMk ((totalToCenterPlus R).app K).hom
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    have hn :=
      (CochainComplex.Plus.ι (twoChartLine R).Modules).congr_map
        ((totalToCenterPlus R).naturality f)
    dsimp only [Functor.map_comp, Functor.comp_map, CochainComplex.Plus.ι,
      ObjectProperty.ι, inducedFunctor, FlasqueCoefficients.toPlus, ObjectProperty.lift,
      ObjectProperty.homMk, center, centerRaw, sourceTotalPlus, rightQPlus,
      rightQTotal, rightQ, rightQRaw, FlasqueBoundedBelow.total, godementTotalPlus,
      Functor.mapCochainComplexPlus] at hn ⊢
    exact hn

/-- The first model arrow is a genuine quasi-isomorphism on the original complexes. -/
lemma thirdToCenter_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((thirdToCenter R).app K) := by
  let : QuasiIso ((thirdToCenterPlus R).app K).hom := thirdToCenterPlus_quasiIso R K
  let : IsIso (((FlasqueDiagonal.EPlusIso R .third).hom.app K).hom) :=
    inferInstanceAs (IsIso ((CochainComplex.Plus.ι (twoChartLine R).Modules).map
      ((FlasqueDiagonal.EPlusIso R .third).hom.app K)))
  change QuasiIso (((FlasqueDiagonal.EPlusIso R .third).hom.app K).hom ≫
    ((thirdToCenterPlus R).app K).hom)
  infer_instance

/-- The second model arrow is the actual proved quasi-isomorphism from the source total. -/
lemma totalToCenter_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((totalToCenter R).app K) :=
  totalToCenterPlus_quasiIso R K

local instance toPlus_additive (X : Scheme.{u}) : (FlasqueCoefficients.toPlus X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    rfl

local instance totalPlus_additive (X : Scheme.{u}) : (godementTotalPlus X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (godementTotal X).map (f.hom + g.hom) =
      (godementTotal X).map f.hom + (godementTotal X).map g.hom
    exact (godementTotal X).map_add

local instance plusMap_additive {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] : F.mapCochainComplexPlus.Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (F.mapHomologicalComplex (.up ℤ)).map (f.hom + g.hom) =
      (F.mapHomologicalComplex (.up ℤ)).map f.hom +
        (F.mapHomologicalComplex (.up ℤ)).map g.hom
    exact (F.mapHomologicalComplex (.up ℤ)).map_add

instance centerRaw_additive (R : CommRingCat.{u}) : (centerRaw R).Additive := by
  dsimp [centerRaw, centerPlus, rightQPlus, sectionRepeatedTotalImage, sectionTotalImage]
  infer_instance

instance center_additive (R : CommRingCat.{u}) : (center R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    exact (centerRaw R).map_add

/-- The actual product total provides the flasque kernel for ordinary second pushforward. -/
lemma centerTotal_flasque (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((godementTotal (relativeSquare R)).obj (centerInputPlus R K).obj).X n).presheaf := by
  obtain ⟨a, ha⟩ := (centerInputPlus R K).property
  let := ha
  exact godementTotal_isFlasque (centerInputPlus R K).obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE (centerInputPlus R K).obj a i hi) n

/-- The original section image of the source total, before product totalization. -/
def centerSectionRaw (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (relativeSquare R) :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    (quotientTensor R).mapHomologicalComplex (.up ℤ) ⋙ godementTotal (twoChartLine R) ⋙
      (Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)

instance centerSectionRaw_additive (R : CommRingCat.{u}) :
    (centerSectionRaw R).Additive := by
  dsimp only [centerSectionRaw]
  infer_instance

/-- The actual section image retains each specified original source lower bound. -/
lemma centerSectionRaw_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((centerSectionRaw R).obj K).IsStrictlyGE a := by
  let : ((rightQTotal R).obj K).obj.IsStrictlyGE a := rightQTotal_isStrictlyGE R K a
  change CochainComplex.IsStrictlyGE
    (((Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)).obj
      ((rightQTotal R).obj K).obj) a
  infer_instance

/-- Finite-line tensor, source total and exact closed section preserve the actual sequence. -/
lemma centerSectionRaw_shortExact (R : CommRingCat.{u})
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (centerSectionRaw R)).ShortExact := by
  let Q := (quotientTensor R).mapHomologicalComplex (.up ℤ)
  let T := godementTotal (twoChartLine R)
  let D := (Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)
  have hQ := hS.map_of_exact Q
  have hT := godementTotal_shortExact hQ
  simpa only [centerSectionRaw, ShortComplex.map_comp] using hT.map_of_exact D

/-- A product total has a flasque lower-bounded kernel for actual ordinary second pushforward. -/
lemma centerTotalPush_shortExact (R : CommRingCat.{u})
    (S : ShortComplex (Complex (relativeSquare R))) (hS : S.ShortExact)
    (a : ℤ) [S.X₁.IsStrictlyGE a] :
    (S.map (godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ))).ShortExact :=
    by
  simp only [ShortComplex.map_comp]
  have hT := godementTotal_shortExact hS
  have hf := godementTotal_isFlasque S.X₁ a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE S.X₁ a i hi)
  exact pushforwardComplex_shortExact_of_flasque_kernel (relativeSecond R) hT hf

/-- The original raw cochain factors of the center, with explicit functor composition. -/
def centerExplicitRaw (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  centerSectionRaw R ⋙ godementTotal (relativeSquare R) ⋙
    (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)

instance centerExplicitRaw_additive (R : CommRingCat.{u}) :
    (centerExplicitRaw R).Additive := by
  dsimp only [centerExplicitRaw]
  infer_instance

/-- The literal center's proof-forgetting factors retain its original raw cochain functors. -/
def centerRawUnderlyingIso (R : CommRingCat.{u}) :
    centerRaw R ≅ centerExplicitRaw R := by
  let A := rightQPlus R
  let T := godementTotalPlus (twoChartLine R)
  let D := (Scheme.Modules.pushforward (relativeDiagonal R)).mapCochainComplexPlus
  let V := godementTotalPlus (relativeSquare R)
  let P := (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  let J := CochainComplex.Plus.ι (relativeSquare R).Modules
  let Qr := (quotientTensor R).mapHomologicalComplex (.up ℤ)
  let Tr := godementTotal (twoChartLine R)
  let Dr := (Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)
  let Vr := godementTotal (relativeSquare R)
  let Pr := (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)
  let B := (FlasqueBoundedBelow.objects (twoChartLine R)).ι
  let eA : A ⋙ I ≅ B ⋙ Qr :=
    associator (FlasqueCoefficients.toPlus (twoChartLine R))
        (quotientTensor R).mapCochainComplexPlus I ≪≫
      isoWhiskerLeft (FlasqueCoefficients.toPlus (twoChartLine R))
        (quotientTensor R).mapCochainComplexPlusCompι ≪≫
      (associator (FlasqueCoefficients.toPlus (twoChartLine R)) I Qr).symm ≪≫
      isoWhiskerRight (FlasqueDiagonal.toPlusUnderlyingIso (twoChartLine R)) Qr
  let eV := forgetComposeIso V P Vr Pr J J I
    (FlasqueDiagonal.totalPlusUnderlyingIso (relativeSquare R))
    (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlusCompι
  let eD := forgetComposeIso D (V ⋙ P) Dr (Vr ⋙ Pr) I J I
    (Scheme.Modules.pushforward (relativeDiagonal R)).mapCochainComplexPlusCompι eV
  let eT := forgetComposeIso T (D ⋙ V ⋙ P) Tr (Dr ⋙ Vr ⋙ Pr) I I I
    (FlasqueDiagonal.totalPlusUnderlyingIso (twoChartLine R)) eD
  exact forgetComposeIso A (T ⋙ D ⋙ V ⋙ P) Qr (Tr ⋙ Dr ⋙ Vr ⋙ Pr) B I I eA eT ≪≫
    isoWhiskerLeft B
      (isoWhiskerLeft Qr (associator Tr Dr (Vr ⋙ Pr)).symm ≪≫
        (associator Qr (Tr ⋙ Dr) (Vr ⋙ Pr)).symm) ≪≫
    (associator B (Qr ⋙ Tr ⋙ Dr) (Vr ⋙ Pr)).symm

/-- The explicit original product-total kernel has flasque terms with the retained input bound. -/
lemma centerTotalRaw_flasque (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque
      (((godementTotal (relativeSquare R)).obj
        (((Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)).obj
          ((godementTotal (twoChartLine R)).obj ((rightQRaw R).obj K)))).X n).presheaf := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  let C := (godementTotal (twoChartLine R)).obj ((rightQRaw R).obj K)
  let : C.IsStrictlyGE a := rightQTotal_isStrictlyGE R K a
  let J := ((Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)).obj C
  let : CochainComplex.IsStrictlyGE J a := inferInstance
  exact godementTotal_isFlasque J a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE J a i hi) n

/-- Original tensor, both exact totals and exact closed section retain the actual raw kernel. -/
lemma centerExplicitRaw_shortExact (R : CommRingCat.{u})
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (centerExplicitRaw R)).ShortExact := by
  obtain ⟨a, ha⟩ := S.X₁.property.1.2
  let := ha
  let : ((S.map (centerSectionRaw R)).X₁).IsStrictlyGE a :=
    centerSectionRaw_isStrictlyGE R S.X₁ a
  simp only [centerExplicitRaw, ShortComplex.map_comp]
  simpa only [ShortComplex.map_comp] using centerTotalPush_shortExact R (S.map (centerSectionRaw R))
    (centerSectionRaw_shortExact R S hS) a

/-- The actual proof-forgetting comparison transfers raw exactness to the literal center. -/
lemma centerRaw_shortExact (R : CommRingCat.{u})
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (centerRaw R)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (centerRawUnderlyingIso R)).symm
    (centerExplicitRaw_shortExact R S hS)

/-- Exactness of the common original model uses actual flasque-kernel pushforward. -/
def centerExactFunctor (R : CommRingCat.{u}) :
    ExactFunctor (FlasqueDiagonal.modelExactStructure R)
      (FlasqueDiagonal.modelExactStructure R) where
  toFunctor := center R
  map_conflation S hS := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hS
    change (S.map (centerRaw R)).ShortExact
    exact centerRaw_shortExact R S hS

/-- The actual quotient-bearing original cofibrations are preserved. -/
lemma center_cofibration (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof f) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof ((center R).map f) :=
  (centerExactFunctor R).map_inflation f hf

/-- The actual source-total weak natural transformation gives preservation of weak arrows. -/
lemma center_weak (R : CommRingCat.{u})
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq f) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((center R).map f) := by
  let : QuasiIso ((rightQTotal R).map f).hom := (rightQTotal_exact R).weak f hf
  let : QuasiIso ((totalToCenter R).app K).hom := totalToCenter_weak R K
  let : QuasiIso ((totalToCenter R).app L).hom := totalToCenter_weak R L
  have hn := (totalToCenter R).naturality f
  have hcomp : QuasiIso
      (((totalToCenter R).app K).hom ≫ ((center R).map f).hom) := by
    have hm := (FlasqueBoundedBelow.objects (twoChartLine R)).ι.congr_map hn
    dsimp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom] at hm
    rw [← hm]
    infer_instance
  exact quasiIso_of_comp_left ((totalToCenter R).app K).hom ((center R).map f).hom

/-- The common original model preserves zero, cofibrations, weak arrows and their pushouts. -/
lemma center_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (center R) where
  zero h := (center R).map_isZero h
  cofibration f hf := center_cofibration R f hf
  weak f hf := center_weak R f hf
  pushout hi h := (centerExactFunctor R).map_isPushout hi h

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint
