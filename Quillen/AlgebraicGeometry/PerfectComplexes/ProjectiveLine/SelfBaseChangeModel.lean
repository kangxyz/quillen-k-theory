/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeAlpha
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback

/-!
# The exact original self-base-change endpoint functors

The source endpoint is the literal flat pullback of actual ordinary projection.
The target endpoint is literal second projection of Godement total of first
pullback. Its perfection is transferred by the proved ORIGINAL alpha; no general
perfect-pushforward premise for the second projection is imposed.
-/
@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange

/-- Literal flat pullback with the original existential strict lower bound. -/
def boundedFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    BoundedBelow.Obj Y ⥤ BoundedBelow.Obj X :=
  ObjectProperty.lift _ ((BoundedBelow.objects Y).ι ⋙ pullbackComplex f) (fun K => by
    obtain ⟨hp, a, ha⟩ := K.property
    let := ha
    refine ⟨locallyPerfect_flatPullback f hp, a, ?_⟩
    apply (CochainComplex.isStrictlyGE_iff _ a).mpr
    intro n hn
    exact (Scheme.Modules.pullback f).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn))

instance boundedFlatPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (boundedFlatPullback f).Additive := by
  unfold boundedFlatPullback
  infer_instance

/-- Every specified original lower bound is retained by flat pullback. -/
lemma boundedFlatPullback_isStrictlyGE {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (K : BoundedBelow.Obj Y) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((boundedFlatPullback f).obj K).obj.IsStrictlyGE a := by
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pullback f).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)

/-- Flat pullback preserves the inherited actual short exact sequences. -/
def boundedFlatPullbackExactFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex Y))
      (BoundedBelow.objects Y))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex X))
      (BoundedBelow.objects X)) where
  toFunctor := boundedFlatPullback f
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects Y).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects Y).ι).map (pullbackComplex f)).ShortExact
    exact hs.map_of_exact _

lemma boundedFlatPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] : Waldhausen.IsExact
    (BoundedBelow.waldhausen Y).cof (BoundedBelow.waldhausen Y).weq
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq
      (boundedFlatPullback f) where
  zero h := (boundedFlatPullback f).map_isZero h
  cofibration s hs := (boundedFlatPullbackExactFunctor f).map_inflation s hs
  weak s hs := by
    change QuasiIso s.hom at hs
    let := hs
    exact pullbackComplex_quasiIso f s.hom
  pushout hi h := (boundedFlatPullbackExactFunctor f).map_isPushout hi h

variable (R : CommRingCat.{u})
local instance modelFirstFlat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- The actual source endpoint p* p_* M, retaining every original chain map. -/
def source : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  FlasqueCoefficients.G0 R ⋙ FlasqueBoundedBelow.inclusion (Spec R) ⋙
    boundedFlatPullback (projection R)

lemma source_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (source R) :=
  (FlasqueCoefficients.G0_exact R).comp
    ((FlasqueBoundedBelow.inclusion_exact (Spec R)).comp
      (boundedFlatPullback_exact (projection R)))

lemma source_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((source R).obj K).obj.IsStrictlyGE a := by
  have : ((FlasqueBoundedBelow.inclusion (Spec R)).obj
      ((FlasqueCoefficients.G0 R).obj K)).obj.IsStrictlyGE a :=
    FlasqueCoefficients.G0Raw_isStrictlyGE R K a
  exact boundedFlatPullback_isStrictlyGE (projection R)
    ((FlasqueBoundedBelow.inclusion (Spec R)).obj ((FlasqueCoefficients.G0 R).obj K)) a

/-- The literal original target complex p2_* T_Z(p1* M). -/
def targetRaw : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ Complex (twoChartLine R) :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙ pullbackComplex (relativeFirst R) ⋙
    godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)

instance targetRaw_additive : (targetRaw R).Additive := by
  unfold targetRaw
  infer_instance

/-- The actual target retains each specified strict lower bound. -/
lemma targetRaw_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((targetRaw R).obj K).IsStrictlyGE a := by
  let A := (boundedFlatPullback (relativeFirst R)).obj
    ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj K)
  have : ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj K).obj.IsStrictlyGE a :=
    inferInstanceAs (K.obj.IsStrictlyGE a)
  have : A.obj.IsStrictlyGE a := boundedFlatPullback_isStrictlyGE (relativeFirst R) _ a
  have : ((godementTotal (relativeSquare R)).obj A.obj).IsStrictlyGE a :=
    godementTotal_isStrictlyGE A.obj a
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE A.obj a n hn)
  apply (CochainComplex.isStrictlyGE_iff _ a).mpr
  intro n hn
  exact (Scheme.Modules.pushforward (relativeSecond R)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE
      ((godementTotal (relativeSquare R)).obj A.obj) a n hn)

/-- Actual first pullback, totalization and second projection have flasque target terms. -/
lemma targetRaw_isFlasque (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((targetRaw R).obj K).X n).presheaf := by
  let A := (boundedFlatPullback (relativeFirst R)).obj
    ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj K)
  let : TopCat.Presheaf.IsFlasque
    (((godementTotal (relativeSquare R)).obj A.obj).X n).presheaf :=
    (FlasqueBoundedBelow.godement_objects A.property).2 n
  change TopCat.Presheaf.IsFlasque
    ((Scheme.Modules.pushforward (relativeSecond R)).obj
      (((godementTotal (relativeSquare R)).obj A.obj).X n)).presheaf
  infer_instance

/-- Target perfection follows from the actual alpha and accepted P2 source perfection. -/
lemma target_objects (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    FlasqueBoundedBelow.objects (twoChartLine R) ((targetRaw R).obj K) := by
  have : QuasiIso ((alphaPlus R).app K).hom := alphaPlus_quasiIso R K
  refine ⟨⟨?_, ((targetPlus R).obj K).property⟩, targetRaw_isFlasque R K⟩
  exact (locallyPerfect_iff_of_quasiIso ((alphaPlus R).app K).hom).mp
    (((source R).obj K).property.1)

/-- The actual target as an original flasque lower-bounded perfect object. -/
def target : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ (targetRaw R) (target_objects R)

instance target_additive : (target R).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (targetRaw R).map (f + g) = (targetRaw R).map f + (targetRaw R).map g
    exact CategoryTheory.Functor.map_add (targetRaw R)

/-- Actual short exact sequences are preserved using the proved flasque-kernel theorem. -/
lemma targetRaw_shortExact {S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R))}
    (hs : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    (S.map (targetRaw R)).ShortExact := by
  let S₀ := S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι
  let S₁ := S₀.map (pullbackComplex (relativeFirst R))
  let S₂ := S₁.map (godementTotal (relativeSquare R))
  have ha : S₁.ShortExact := hs.map_of_exact (pullbackComplex (relativeFirst R))
  have ht : S₂.ShortExact := godementTotal_shortExact ha
  have hfl : ∀ n, TopCat.Presheaf.IsFlasque (S₂.X₁.X n).presheaf := by
    let A := (boundedFlatPullback (relativeFirst R)).obj
      ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj S.X₁)
    exact (FlasqueBoundedBelow.godement_objects A.property).2
  have hpush := pushforwardComplex_shortExact_of_flasque_kernel (relativeSecond R) ht hfl
  simpa only [targetRaw, ShortComplex.map_comp] using hpush

/-- The target exactness uses flat pullback, exact total, then ONLY flasque-kernel pushforward. -/
def targetExactFunctor : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (FlasqueBoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (FlasqueBoundedBelow.objects (twoChartLine R))) where
  toFunctor := target R
  map_conflation S hs := by
    change (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact at hs
    change ((S.map (target R)).map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact
    rw [← ShortComplex.map_comp]
    change (S.map (targetRaw R)).ShortExact
    exact targetRaw_shortExact R hs

/-- Forgetting the source lower-bound proof retains the literal original source map. -/
lemma sourcePlus_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((sourcePlus R).map f).hom = ((source R).map f).hom := rfl

/-- Forgetting the target lower-bound proof retains the literal original target map. -/
lemma targetPlus_map_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((targetPlus R).map f).hom = (targetRaw R).map f := rfl

/-- The original alpha naturality in the actual underlying chain category. -/
lemma alphaPlus_naturality_hom {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((sourcePlus R).map f).hom ≫ ((alphaPlus R).app L).hom =
      ((alphaPlus R).app K).hom ≫ ((targetPlus R).map f).hom :=
  congrArg (CochainComplex.Plus.ι (twoChartLine R).Modules).map
    ((alphaPlus R).naturality f)

/-- Actual alpha naturality and two-out-of-three preserve the original target weak arrows. -/
lemma targetRaw_weak {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq f) :
    QuasiIso ((targetRaw R).map f) := by
  have : QuasiIso (((source R).map f).hom) := (source_exact R).weak f hf
  have : QuasiIso ((alphaPlus R).app K).hom := alphaPlus_quasiIso R K
  have : QuasiIso ((alphaPlus R).app L).hom := alphaPlus_quasiIso R L
  have hc : QuasiIso (((source R).map f).hom ≫ ((alphaPlus R).app L).hom) := inferInstance
  have hn := alphaPlus_naturality_hom R f
  rw [sourcePlus_map_hom, targetPlus_map_hom] at hn
  rw [hn] at hc
  exact quasiIso_of_comp_left ((alphaPlus R).app K).hom ((targetRaw R).map f)

lemma target_weak {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L)
    (hf : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq f) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((target R).map f) :=
  targetRaw_weak R f hf

/-- The target is a genuine exact functor of the original Waldhausen model. -/
lemma target_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (target R) where
  zero h := (target R).map_isZero h
  cofibration s hs := (targetExactFunctor R).map_inflation s hs
  weak s hs := target_weak R s hs
  pushout hi h := (targetExactFunctor R).map_isPushout hi h

end Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
