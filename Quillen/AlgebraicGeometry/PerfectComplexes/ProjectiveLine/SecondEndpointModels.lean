/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SecondEndpointUnderlying
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.WeakFunctorOpaque

/-!
# Actual exact model functors for the literal second endpoint span

The source is original left Q tensor of actual p* p_* K, then original T_P.
The center is original T_P of V. V is perfect by the original beta weak arrow
from Q tensor U and the original base-change target perfection theorem.
-/

@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint

variable (R : CommRingCat.{u})
local instance firstFlat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- Original left Q tensor on the actual lower-bounded perfect carrier. -/
def quotientLeftBounded : BoundedBelow.Obj (twoChartLine R) ⥤
    BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ ((BoundedBelow.objects (twoChartLine R)).ι ⋙
    tensorByLineComplex (tautologicalQuotientLine R)) (fun K => by
      obtain ⟨hp, a, ha⟩ := K.property
      let := ha
      refine ⟨FlasqueDiagonal.quotientLeft_locallyPerfect R K.obj hp, a, ?_⟩
      apply (CochainComplex.isStrictlyGE_iff _ a).mpr
      intro n hn
      exact (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R)).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance quotientLeftBounded_additive : (quotientLeftBounded R).Additive := by
  unfold quotientLeftBounded
  infer_instance

lemma quotientLeftBounded_isStrictlyGE (K : BoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((quotientLeftBounded R).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- Exact left tensor retains the actual inherited quotient-bearing sequences. -/
def quotientLeftBoundedExactFunctor : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := quotientLeftBounded R
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects (twoChartLine R)).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects (twoChartLine R)).ι).map
      (tensorByLineComplex (tautologicalQuotientLine R))).ShortExact
    exact hs.map_of_exact _

lemma quotientLeftBounded_exact : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (quotientLeftBounded R) where
  zero h := (quotientLeftBounded R).map_isZero h
  cofibration a ha := (quotientLeftBoundedExactFunctor R).map_inflation a ha
  weak a ha := by
    change QuasiIso a.hom at ha
    let := ha
    change QuasiIso ((tensorByLineComplex (tautologicalQuotientLine R)).map a.hom)
    unfold tensorByLineComplex
    infer_instance
  pushout hi h := (quotientLeftBoundedExactFunctor R).map_isPushout hi h

/-- Literal Q tensor p* p_* K before original outer total. -/
def sourceBounded : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    BoundedBelow.Obj (twoChartLine R) :=
  SelfBaseChange.source R ⋙ quotientLeftBounded R

/-- Literal source T_P(Q LEFT tensor p* p_* K) in the original flasque model. -/
def source : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  sourceBounded R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma sourceBounded_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (sourceBounded R) :=
  (SelfBaseChange.source_exact R).comp (quotientLeftBounded_exact R)

lemma source_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (source R) :=
  (sourceBounded_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

lemma source_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((source R).obj K).obj.IsStrictlyGE a := by
  let S := (SelfBaseChange.source R).obj K
  let : S.obj.IsStrictlyGE a := SelfBaseChange.source_isStrictlyGE R K a
  let : ((sourceBounded R).obj K).obj.IsStrictlyGE a :=
    quotientLeftBounded_isStrictlyGE R S a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R)
    ((sourceBounded R).obj K) a

/-- Literal original left Q tensor of U before total, used for V perfection. -/
def tensorURaw : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  SelfBaseChange.targetRaw R ⋙ tensorByLineComplex (tautologicalQuotientLine R)

lemma tensorURaw_locallyPerfect (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((tensorURaw R).obj K) :=
  FlasqueDiagonal.quotientLeft_locallyPerfect R ((SelfBaseChange.targetRaw R).obj K)
    (SelfBaseChange.target_objects R K).1.1

/-- V perfection is transferred through the ACTUAL original beta from Q tensor U. -/
lemma VRaw_locallyPerfect (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    locallyPerfect (twoChartLine R) ((VRaw R).obj K) := by
  let : QuasiIso ((beta R).app K).hom := beta_quasiIso R K
  exact (locallyPerfect_iff_of_quasiIso ((beta R).app K).hom).mp
    (tensorURaw_locallyPerfect R K)

/-- Actual V has all three required properties before any outer total. -/
lemma VRaw_objects (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (twoChartLine R) ((VRaw R).obj K) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  exact ⟨⟨VRaw_locallyPerfect R K, a, VPlus_isStrictlyGE R K a⟩, VPlus_flasque R K⟩

/-- Literal V in the original full flasque-perfect carrier. -/
def V : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (VRaw R) (VRaw_objects R)

instance V_additive : (V R).Additive where
  map_add := by
    intro K L a b
    apply ObjectProperty.hom_ext
    exact (VRaw R).map_add

/-- Flat first pullback and exact original total retain the actual input sequence. -/
lemma CRaw_shortExact (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hs : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (CRaw R)).ShortExact := by
  let P := (Scheme.Modules.pullback (relativeFirst R)).mapHomologicalComplex (.up ℤ)
  have hp := hs.map_of_exact P
  have hc := godementTotal_shortExact hp
  have hn : (S.map (CNative R)).ShortExact := by
    simpa only [CNative, ShortComplex.map_comp] using hc
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (CUnderlyingIso R).symm) hn

/-- Exact left tensor and total, followed ONLY by flasque-kernel ordinary second image. -/
lemma VRaw_shortExact (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hs : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (VRaw R)).ShortExact := by
  let T := (squareTensor R).mapHomologicalComplex (.up ℤ)
  have hc := CRaw_shortExact R S hs
  have ht := hc.map_of_exact T
  have hg := godementTotal_shortExact ht
  have hfl : ∀ n, TopCat.Presheaf.IsFlasque
      ((((S.map (CRaw R)).map T).map (godementTotal (relativeSquare R))).X₁.X n).presheaf := by
    obtain ⟨a, ha⟩ := S.X₁.property.1.2
    let := ha
    let B := (squareTensor R).mapCochainComplexPlus.obj ((CPlus R).obj S.X₁)
    let : B.obj.IsStrictlyGE a := tensorCPlus_isStrictlyGE R S.X₁ a
    exact godementTotal_isFlasque B.obj a
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE B.obj a i hi)
  have hpush := pushforwardComplex_shortExact_of_flasque_kernel (relativeSecond R) hg hfl
  have hn : (S.map (VNative R)).ShortExact := by
    simpa only [VNative, ShortComplex.map_comp] using hpush
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (VUnderlyingIso R).symm) hn

def VExactFunctor : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (FlasqueBoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (FlasqueBoundedBelow.objects (twoChartLine R))) where
  toFunctor := V R
  map_conflation S hs := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hs
    change ((S.map (V R)).map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact
    rw [← ShortComplex.map_comp]
    change (S.map (VRaw R)).ShortExact
    exact VRaw_shortExact R S hs

/-- Original flat first pullback and total preserve the actual input weak map. -/
lemma CPlus_weak {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L)
    (ha : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq a) :
    QuasiIso ((CPlus R).map a).hom := by
  change QuasiIso a.hom at ha
  let := ha
  let b := (firstPlus R).map a
  let : QuasiIso b.hom := by
    change QuasiIso (((Scheme.Modules.pullback
      (relativeFirst R)).mapHomologicalComplex (.up ℤ)).map a.hom)
    infer_instance
  exact godementTotalPlus_map_quasiIso b

/-- Functor-level equality retains the entire original plain object/map expression. -/
lemma VNative_eq : VNative R =
    plusTensorTotalImageFunctor (relativeSecond R) (CPlus R) (squareTensor R) := by
  unfold VNative CRaw plusTensorTotalImageFunctor
  rfl

/-- Weak maps use exact line tensor and image only BETWEEN THE ACTUAL TOTALS. -/
lemma VNative_weak {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L)
    (ha : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq a) :
    QuasiIso ((VNative R).map a) := by
  rw [VNative_eq]
  exact plusTensorTotalImageFunctor_map_quasiIso (relativeSecond R)
    (CPlus R) (squareTensor R) (K := K) (L := L) a (CPlus_weak R a ha)

/-- Canonical proof-forgetting naturality transports the fixed native weak map. -/
lemma VRaw_weak {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L)
    (ha : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq a) :
    QuasiIso ((VRaw R).map a) :=
  complex_map_quasiIso_of_natIso (F := VRaw R) (G := VNative R)
    (VUnderlyingIso R) (K := K) (L := L) a (VNative_weak R a ha)

lemma V_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (V R) where
  zero h := (V R).map_isZero h
  cofibration a ha := (VExactFunctor R).map_inflation a ha
  weak a ha := VRaw_weak R a ha
  pushout hi h := (VExactFunctor R).map_isPushout hi h

/-- The literal common center T_P(V), in the original flasque model. -/
def center : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  V R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) ⋙
    FlasqueBoundedBelow.total (twoChartLine R)

lemma center_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (center R) :=
  (V_exact R).comp ((FlasqueBoundedBelow.inclusion_exact (twoChartLine R)).comp
    (FlasqueBoundedBelow.total_exact (twoChartLine R)))

lemma center_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((center R).obj K).obj.IsStrictlyGE a := by
  let : ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj
      ((V R).obj K)).obj.IsStrictlyGE a := VPlus_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R)
    ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj ((V R).obj K)) a

end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
