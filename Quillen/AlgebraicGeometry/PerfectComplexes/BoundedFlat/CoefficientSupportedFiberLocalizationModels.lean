/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenKZeroExact
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull
public import Quillen.Waldhausen.Fibration.Rows.JointRetarget
public import Quillen.CategoryTheory.ObjectProperty.LiftInclusion
public import Quillen.Waldhausen.SmallModel.Composition
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence
public import Quillen.Waldhausen.Fibration.ConeComparison
public import Quillen.Topology.Prespectrum.ConeStableNaturality
public import Quillen.Topology.Prespectrum.ConeDescNaturality

/-!
# Original auxiliary-supported native fiber, ambient and coarse cone

The actual native intersection support is vanishing on the union of the
original auxiliary open and original localization open. Its literal inclusion
into auxiliary support, the unchanged coarse weakness and their joint zero
construct the same coefficient-natural reversed zero-to-inclusion whole null.

Actual supported joint cylinders transport through genuine ordinary exact
evaluation. The transported second endpoint, original weak predicate and
extension with the genuine image zero prove the native fibration theorem.
Literal native acyclic conversion and AsSmall.up then retain the actual chosen
joint zero and every canonical null time in the original cone comparison.

No independently chosen geometric zeros are identified. The initial cone
result requires no compactness or separation and asserts no seed, telescope
or classical nonconnective K-theory comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.CoefficientBaseChange HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- Original intersection support implies the unchanged auxiliary support. -/
theorem boundedFlatCoefficientFiberSupport_le (a : Under R) :
    boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι ≤
      boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι := by
  intro S hS
  exact ((restrictAcyclic_sup_iff (boundedFlatCoefficientSupportOpen Q T a)
    (schemeMap f a).opensRange
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S).obj).mp hS).1

/-- Forget only the additional closed fiber support, keeping the actual native section. -/
def boundedFlatCoefficientSupportedFiberForget (a : Under R) :
    BoundedFlatCoefficientSupportedFiberSections f T a ⥤
      BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a :=
  ObjectProperty.ιOfLE (boundedFlatCoefficientFiberSupport_le f T a)

private theorem propertyEvaluation_forget {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (hPQ : P ≤ Q) (A B : ObjectProperty D) (hAB : A ≤ B)
    (E : C ⥤ D) (hEA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hEB : ∀ X : Q.FullSubcategory, B (E.obj X.obj)) :
    A.lift (P.ι ⋙ E) hEA ⋙ ObjectProperty.ιOfLE hAB =
      ObjectProperty.ιOfLE hPQ ⋙ B.lift (Q.ι ⋙ E) hEB := rfl

/-- Original intersection support inclusion after evaluation keeps the actual complex. -/
theorem boundedFlatCoefficientSupportedFiberEvaluation_forget (a : Under R) :
    boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientFiberSupportOpen f T a).ι ⋙
      ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι ≤
          boundedFlatPerfectSupported (boundedFlatCoefficientSupportOpen Q T a).ι from
          fun K hK ↦ ((boundedFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a) K).mp hK).1) =
      boundedFlatCoefficientSupportedFiberForget f T a ⋙
        boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι := by
  unfold boundedFlatCoefficientSupportedEvaluation
  dsimp only [boundedFlatCoefficientSupportedFiberForget]
  exact propertyEvaluation_forget _ _ _ _ _ _ _ _ _

private theorem supportLift_congr {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) :
    P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- The identity coefficient reindexing square forgets only the extra support open. -/
theorem boundedFlatCoefficientSupportedFiberForget_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.cof
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.weq
      (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.cof
      (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.weq
      (boundedFlatCoefficientSupportedFiberForget f T a) := by
  let l := (space (op Q, a)).homOfLE
    (show boundedFlatCoefficientSupportOpen Q T a ≤ boundedFlatCoefficientFiberSupportOpen f T a
      from le_sup_left)
  have h : l ≫ (boundedFlatCoefficientFiberSupportOpen f T a).ι =
      (boundedFlatCoefficientSupportOpen Q T a).ι ≫
        AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op Q, a)) := by
    rw [AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id, Category.comp_id]
    exact Scheme.homOfLE_ι _ _
  have hM : boundedFlatCoefficientSupportedSectionsMap
      (boundedFlatCoefficientFiberSupportOpen f T a).ι
      (boundedFlatCoefficientSupportOpen Q T a).ι (𝟙 (op Q, a)) l h =
      boundedFlatCoefficientSupportedFiberForget f T a := by
    change (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).lift
      ((boundedFlatCoefficientSectionSupported
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι ⋙
        boundedFlatCoefficientSectionsMap (𝟙 (op Q, a))) _ =
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι).lift
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι
          _
    apply supportLift_congr
    exact (congrArg (fun F ↦ (boundedFlatCoefficientSectionSupported
      (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι ⋙ F)
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_id
        (boundedFlatCoefficientProjection R) (op Q, a))).trans (Functor.comp_id _)
  rw [← hM]
  exact boundedFlatCoefficientSupportedSectionsMap_exact
    (boundedFlatCoefficientFiberSupportOpen f T a).ι
    (boundedFlatCoefficientSupportOpen Q T a).ι (𝟙 (op Q, a)) l h

/-- The literal support inclusion retains the original restricted joint zero. -/
def boundedFlatCoefficientSupportedFiberForgetModelMap (a : Under R) :
    boundedFlatCoefficientSupportedFiberModel f T a ⟶
      boundedFlatCoefficientSupportedAmbientModel T a where
  functor := boundedFlatCoefficientSupportedFiberForget f T a
  exact := boundedFlatCoefficientSupportedFiberForget_exact f T a
  zero := rfl

/-- Every original coefficient map preserves the same intersection-support inclusion. -/
def boundedFlatCoefficientSupportedFiberForgetModelTransformation :
    boundedFlatCoefficientSupportedFiberModelFunctor f T ⟶
      boundedFlatCoefficientSupportedAmbientModelFunctor T where
  app := boundedFlatCoefficientSupportedFiberForgetModelMap f T
  naturality a b g := by
    apply Model.Hom.ext
    rfl

/-- Original native fine ambient prespectra retaining auxiliary closed support. -/
def boundedFlatCoefficientSupportedAmbientPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor

/-- Original native fine prespectra on the actual intersection of the closed supports. -/
def boundedFlatCoefficientSupportedFiberPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor

/-- Original realization of the actual intersection-support inclusion. -/
def boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation :
    boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T :=
  Functor.whiskerRight (boundedFlatCoefficientSupportedFiberForgetModelTransformation f T)
    prespectrumFunctor

/-- Original supported ambient identity change to the relative-open coarse weakness. -/
def boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation :
    boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T ⟶
      boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  Functor.whiskerRight (boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    prespectrumFunctor

/-- The unique original zero-to-intersection-support inclusion transformation. -/
def boundedFlatCoefficientSupportedFiberZeroToOpen (a : Under R) :
    (Functor.const (BoundedFlatCoefficientSupportedFiberSections f T a)).obj
      (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.zero ⟶
        boundedFlatCoefficientSupportedFiberForget f T a where
  app S := (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.isZero.to_
    ((boundedFlatCoefficientSupportedFiberForget f T a).obj S)
  naturality _ _ _ :=
    (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.isZero.eq_of_src _ _

/-- Actual intersection support makes this same zero-to-inclusion transformation coarse weak. -/
theorem boundedFlatCoefficientSupportedFiberZeroToOpen_weak (a : Under R)
    (S : BoundedFlatCoefficientSupportedFiberSections f T a) :
    (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.weq
      ((boundedFlatCoefficientSupportedFiberZeroToOpen f T a).app S) := by
  change (boundedFlatCoefficientSupportedOpenWaldhausen f T a).weq _
  apply (boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a _).mpr
  let N := boundedFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)
  let K := (boundedFlatCoefficientSupportedEvaluation
    (boundedFlatCoefficientSupportOpen Q T a).ι).obj
      ((boundedFlatCoefficientSupportedFiberForget f T a).obj S)
  have hK : Acyclic N.coarse K := by
    apply (boundedFlatPerfectSupportedOpenAcyclic_iff (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) K).mpr
    dsimp only [K]
    rw [boundedFlatCoefficientSupportedEvaluation_obj]
    exact (boundedFlatCoefficientFiberSupported_iff f T a
      ((boundedFlatCoefficientSupportedFiberForget f T a).obj S)).mp S.property
  have hZ : IsZero ((boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientSupportOpen Q T a).ι).obj
      (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.zero) :=
    boundedFlatCoefficientSupportedEvaluation_sectionZero_isZero _
  have hp : (boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientSupportOpen Q T a).ι).map
      ((boundedFlatCoefficientSupportedFiberZeroToOpen f T a).app S) = hZ.to_ K :=
    hZ.eq_of_src _ _
  rw [hp]
  exact (acyclic_iff_weak_from_isZero N.coarse hZ K).mp hK

/-- Reverse the original weak zero-to-inclusion realization with every time retained. -/
def boundedFlatCoefficientSupportedFiberOpenDiagramNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
      (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T) :=
  modelDiagramZeroNull (boundedFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    (boundedFlatCoefficientSupportedFiberZeroToOpen f T)
    (boundedFlatCoefficientSupportedFiberZeroToOpen_weak f T)

/-- The original native intersection-support cone descends along the same complete null. -/
def boundedFlatCoefficientSupportedFiberOpenConeComparison :
    mappingConeDiagram (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) ⟶
      boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation
    f T) (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).naturality


/-- The original ambient cone face is precisely the actual supported change of weakness. -/
theorem boundedFlatCoefficientSupportedFiberOpenConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
      ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a) ≫
      (boundedFlatCoefficientSupportedFiberOpenConeComparison f T).app a =
      (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a :=
  mappingConeInclusion_desc _ _ _

/-- Each original cone cylinder retains the actual canonical support-null time. -/
theorem boundedFlatCoefficientSupportedFiberOpenConeComparison_cylinder
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space m) :
    ((boundedFlatCoefficientSupportedFiberOpenConeComparison f T).app a).map m
      (Quillen.ReducedMappingCone.cylinder
        (((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).point m)
        (((boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T).obj a).point m)
        (((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a).map m)
        (s, x)) =
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level m (s, x) := rfl




private theorem twoOutOfThree_of_evaluation {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    [W.weq.HasTwoOutOfThreeProperty]
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p)) :
    V.weq.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    apply (hw _).mpr
    rw [F.map_comp]
    exact W.weq.comp_mem _ _ ((hw _).mp hf) ((hw _).mp hg)
  of_postcomp f g hg hfg := by
    apply (hw _).mpr
    apply W.weq.of_postcomp (W' := W.weq) _ (F.map g) ((hw _).mp hg)
    simpa only [F.map_comp] using (hw _).mp hfg
  of_precomp f g hf hfg := by
    apply (hw _).mpr
    apply W.weq.of_precomp (W' := W.weq) (F.map f) _ ((hw _).mp hf)
    simpa only [F.map_comp] using (hw _).mp hfg

private theorem extension_of_evaluation {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p))
    (he : ExtensionAxiom W) : ExtensionAxiom V where
  extension hi hi' h h' a b c wi wq ha hc := by
    apply (hw _).mpr
    let hZ := hF.zero V.isZero
    have mapped {X Y S : C} {j : X ⟶ Y} {r : Y ⟶ S}
        (hj : V.cof j) (hp : IsPushout j (V.isZero.from_ X) r (V.isZero.to_ S)) :
        IsPushout (F.map j) (hZ.from_ (F.obj X)) (F.map r) (hZ.to_ (F.obj S)) := by
      convert! hF.pushout hj hp using 1
      · exact hZ.eq_of_tgt _ _
      · exact hZ.eq_of_src _ _
    exact he.extension_of_isZero hZ (hF.cofibration _ hi) (hF.cofibration _ hi')
      (mapped hi h) (mapped hi' h') (F.map a) (F.map b) (F.map c)
      (by simpa only [F.map_comp] using congrArg F.map wi)
      (by simpa only [F.map_comp] using congrArg F.map wq)
      ((hw _).mp ha) ((hw _).mp hc)

private theorem equivalenceJoint_secondEndpoint {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (e : C ≌ D)
    (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
    (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
    (J : RowFactorization.JointData (NestedWeakEquivalences.refl V))
    (hJ : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) J) :
    RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W)
      (RowFactorization.JointData.ofExactEquivalence V W e hF hG J) := by
  intro f
  change ((e.counitIso.app f.right).inv ≫ e.functor.map (J.inr.app (e.inverse.mapArrow.obj f))) ≫
    e.functor.map (J.joint.obj (e.inverse.mapArrow.obj f)).obj.hom ≫
    (e.functor.map (J.projection.app (e.inverse.mapArrow.obj f)) ≫ (e.counitIso.app f.right).hom) =
      𝟙 _
  have ht := congrArg e.functor.map (hJ (e.inverse.mapArrow.obj f))
  simp only [Functor.map_comp] at ht
  calc
    _ = (e.counitIso.app f.right).inv ≫
        (e.functor.map (J.inr.app (e.inverse.mapArrow.obj f)) ≫
          e.functor.map (J.joint.obj (e.inverse.mapArrow.obj f)).obj.hom ≫
          e.functor.map (J.projection.app (e.inverse.mapArrow.obj f))) ≫ (e.counitIso.app
            f.right).hom := by
            simp only [Category.assoc]
    _ = 𝟙 _ := by rw [ht]; simp

private def supportedNativeJointData (a : Under R) :
    RowFactorization.JointData (boundedFlatCoefficientSupportedOpenNested f T a) :=
  (boundedFlatCoefficientSupportedSectionJointData
    (boundedFlatCoefficientSupportOpen Q T a).ι).toNested
    (boundedFlatCoefficientSupportedOpenNested f T a)

private theorem supportedSectionJoint_secondEndpoint {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] :
    RowFactorization.SecondEndpointSection
      (NestedWeakEquivalences.refl (boundedFlatCoefficientSupportedSectionWaldhausen j))
      (boundedFlatCoefficientSupportedSectionJointData j) :=
  equivalenceJoint_secondEndpoint
    (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatCoefficientSupportedSectionWaldhausen
      j)
    (boundedFlatCoefficientSupportedSectionEquivalence
      j).symm
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      j)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      j)
    (boundedFlatPerfectSupportedJointData j)
    (complexJointDataOfNested_secondEndpointSection
      (boundedFlatPerfectSupported j)
      (fun hK hL p ↦ boundedFlatPerfectSupported_mappingCone
        j hK hL p)
      (fun _ hK ↦ boundedFlatPerfectSupported_shift
        j hK 1) _)


private theorem secondEndpoint_toNested {C : Type*} [Category* C] {V : Structure C}
    (J : RowFactorization.JointData (NestedWeakEquivalences.refl V))
    (N : NestedWeakEquivalences V)
    (hJ : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) J) :
    RowFactorization.SecondEndpointSection N (J.toNested N) := hJ

omit [IsOpenImmersion f.left] in
private theorem supportedNativeJoint_secondEndpoint (a : Under R) :
    RowFactorization.SecondEndpointSection (boundedFlatCoefficientSupportedOpenNested f T a)
      (supportedNativeJointData f T a) :=
  secondEndpoint_toNested (boundedFlatCoefficientSupportedSectionJointData
    (boundedFlatCoefficientSupportOpen Q T a).ι) (boundedFlatCoefficientSupportedOpenNested f T a)
    (supportedSectionJoint_secondEndpoint (boundedFlatCoefficientSupportOpen Q T a).ι)

private theorem supportedNative_canonicalCone_isStableEquivalence (a : Under R) :
    IsStableEquivalence
      (canonicalConePrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a)) := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  let W := boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)
  let E := boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι
  have hw : ∀ {X Y} (p : X ⟶ Y), N.coarse.weq p ↔ W.weq (E.map p) :=
    fun p ↦ boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p
  let : W.weq.HasTwoOutOfThreeProperty :=
    instHasTwoOutOfThreePropertyBoundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)
  let : N.coarse.weq.HasTwoOutOfThreeProperty :=
    twoOutOfThree_of_evaluation N.coarse W E hw
  have he : ExtensionAxiom N.coarse :=
    extension_of_evaluation N.coarse W E
      (boundedFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a) hw
      (boundedFlatPerfectSupportedOpenWaldhausen_extensionAxiom (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))
  exact canonicalConePrespectrumMap_isStableEquivalence_general N he
    (supportedNativeJointData f T a) (supportedNativeJoint_secondEndpoint f T a)


private theorem acyclic_evaluation_iff {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p)) (X : C) :
    Acyclic V X ↔ Acyclic W (F.obj X) := by
  let hZ := hF.zero V.isZero
  have hp : F.map (V.isZero.to_ X) = hZ.to_ (F.obj X) := hZ.eq_of_src _ _
  change V.weq (V.isZero.to_ X) ↔ Acyclic W (F.obj X)
  rw [hw, hp]
  exact (acyclic_iff_weak_from_isZero W hZ _).symm

private theorem supportedNativeAcyclic_evaluation_iff (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    Acyclic (boundedFlatCoefficientSupportedOpenNested f T a).coarse S ↔
      Acyclic (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).coarse
        ((boundedFlatCoefficientSupportedEvaluation
          (boundedFlatCoefficientSupportOpen Q T a).ι).obj S) :=
  acyclic_evaluation_iff (boundedFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a)
    (fun p ↦ boundedFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p) S

/-- Original native coarse acyclicity is precisely the true intersection-support condition. -/
theorem boundedFlatCoefficientSupportedOpenAcyclic_iff (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    Acyclic (boundedFlatCoefficientSupportedOpenNested f T a).coarse S ↔
      boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι
        S.obj := by
  rw [supportedNativeAcyclic_evaluation_iff]
  change Acyclic (boundedFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a))
    ((boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientSupportOpen Q T a).ι).obj S) ↔ _
  rw [boundedFlatPerfectSupportedOpenAcyclic_iff, boundedFlatCoefficientSupportedEvaluation_obj]
  exact (boundedFlatCoefficientFiberSupported_iff f T a S).symm

/-- The actual intersection support is exactly acyclicity inside the original native support. -/
def boundedFlatCoefficientSupportedFiberToAcyclic (a : Under R) :
    BoundedFlatCoefficientSupportedFiberSections f T a ⥤
      AcyclicCategory (boundedFlatCoefficientSupportedOpenNested f T a) where
  obj S := ⟨(boundedFlatCoefficientSupportedFiberForget f T a).obj S,
    (boundedFlatCoefficientSupportedOpenAcyclic_iff f T a _).mpr S.property⟩
  map p := ObjectProperty.homMk ((boundedFlatCoefficientSupportedFiberForget f T a).map p)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flatten original native acyclic sections to the actual intersection-support section. -/
def boundedFlatCoefficientSupportedAcyclicToFiber (a : Under R) :
    AcyclicCategory (boundedFlatCoefficientSupportedOpenNested f T a) ⥤
      BoundedFlatCoefficientSupportedFiberSections f T a where
  obj S := ⟨S.obj.obj, (boundedFlatCoefficientSupportedOpenAcyclic_iff f T a S.obj).mp S.property⟩
  map p := ObjectProperty.homMk p.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The native support comparison is a genuine literal flattening equivalence. -/
def boundedFlatCoefficientSupportedFiberAcyclicEquivalence (a : Under R) :
    BoundedFlatCoefficientSupportedFiberSections f T a ≌
      AcyclicCategory (boundedFlatCoefficientSupportedOpenNested f T a) :=
  CategoryTheory.Equivalence.mk
    (boundedFlatCoefficientSupportedFiberToAcyclic f T a)
    (boundedFlatCoefficientSupportedAcyclicToFiber f T a)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl))

/-- The same fine support-forget map is retained literally by native acyclic conversion. -/
theorem boundedFlatCoefficientSupportedFiberToAcyclic_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedFiberToAcyclic f T a ⋙
      acyclicInclusion (boundedFlatCoefficientSupportedOpenNested f T a) =
      boundedFlatCoefficientSupportedFiberForget f T a := rfl


private theorem acyclic_lift_exact {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) {W : Structure D} (N : NestedWeakEquivalences W)
    (F : C ⥤ AcyclicCategory N)
    (h : IsExact V.cof V.weq W.cof W.weq (F ⋙ acyclicInclusion N)) :
    IsExact V.cof V.weq (acyclicStructure N).cof (acyclicStructure N).weq F where
  zero hZ := IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _ (h.zero hZ)
  cofibration p hp := h.cofibration p hp
  weak p hp := h.weak p hp
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects N).ι (h.pushout hi hp)

private theorem supportedNativeFiberToAcyclic_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.cof
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.weq
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatCoefficientSupportedFiberToAcyclic f T a) :=
  acyclic_lift_exact (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen
    (boundedFlatCoefficientSupportedOpenNested f T a)
    (boundedFlatCoefficientSupportedFiberToAcyclic f T a)
    ((boundedFlatCoefficientSupportedFiberToAcyclic_inclusion f T a).symm ▸
      boundedFlatCoefficientSupportedFiberForget_exact f T a)

private def supportedNativeAcyclicEvaluation (a : Under R) :
    AcyclicCategory (boundedFlatCoefficientSupportedOpenNested f T a) ⥤
      AcyclicCategory (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)) :=
  (acyclicObjects (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a))).lift
    (acyclicInclusion (boundedFlatCoefficientSupportedOpenNested f T a) ⋙
      boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι)
    (fun S ↦ (supportedNativeAcyclic_evaluation_iff f T a S.obj).mp S.property)

private theorem supportedNativeAcyclicEvaluation_inclusion (a : Under R) :
    supportedNativeAcyclicEvaluation f T a ⋙
      acyclicInclusion (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)) =
      acyclicInclusion (boundedFlatCoefficientSupportedOpenNested f T a) ⋙
        boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι :=
  Quillen.ObjectProperty.lift_comp_ι _ _ _

private theorem supportedNativeAcyclicEvaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))).cof
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))).weq
      (supportedNativeAcyclicEvaluation f T a) :=
  acyclic_lift_exact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)) (supportedNativeAcyclicEvaluation f T a)
    ((supportedNativeAcyclicEvaluation_inclusion f T a).symm ▸
      (acyclicInclusion_exact (boundedFlatCoefficientSupportedOpenNested f T a)).comp
        (boundedFlatCoefficientSupportedEvaluation_exact
          (boundedFlatCoefficientSupportOpen Q T a).ι))

private theorem nestedEvaluation_flatten {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (R : ObjectProperty P.FullSubcategory)
    (A B : ObjectProperty D) (S : ObjectProperty A.FullSubcategory) (E : C ⥤ D)
    (hQ : ∀ X : R.FullSubcategory, Q X.obj.obj)
    (hA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hB : ∀ X : S.FullSubcategory, B X.obj.obj)
    (hBE : ∀ X : Q.FullSubcategory, B (E.obj X.obj))
    (hS : ∀ X : R.FullSubcategory, S ((A.lift (P.ι ⋙ E) hA).obj X.obj)) :
    ({ obj := fun X ↦ ⟨X.obj.obj, hQ X⟩
       map := fun p ↦ ObjectProperty.homMk p.hom.hom
       map_id := fun _ ↦ rfl
       map_comp := fun _ _ ↦ rfl } : R.FullSubcategory ⥤ Q.FullSubcategory) ⋙
      B.lift (Q.ι ⋙ E) hBE =
      S.lift (R.ι ⋙ A.lift (P.ι ⋙ E) hA) hS ⋙
      ({ obj := fun X ↦ ⟨X.obj.obj, hB X⟩
         map := fun p ↦ ObjectProperty.homMk p.hom.hom
         map_id := fun _ ↦ rfl
         map_comp := fun _ _ ↦ rfl } : S.FullSubcategory ⥤ B.FullSubcategory) := rfl

private theorem supportedNativeAcyclicToFiber_evaluation (a : Under R) :
    boundedFlatCoefficientSupportedAcyclicToFiber f T a ⋙ boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientFiberSupportOpen f T a).ι =
      supportedNativeAcyclicEvaluation f T a ⋙ boundedFlatPerfectSupportedOpenAcyclicToSupported
        (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) := by
  unfold boundedFlatCoefficientSupportedAcyclicToFiber supportedNativeAcyclicEvaluation
    boundedFlatPerfectSupportedOpenAcyclicToSupported
  unfold boundedFlatCoefficientSupportedEvaluation acyclicInclusion
  exact nestedEvaluation_flatten
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (acyclicObjects (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatPerfectSupported (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatPerfectSupported (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (acyclicObjects (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)))
    (boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙
      (boundedFlatPerfect (space (op Q, a))).ι)
    (fun X ↦ (boundedFlatCoefficientSupportedOpenAcyclic_iff f T a X.obj).mp X.property)
    (fun X ↦ ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ (boundedFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) X.obj.obj).mpr
      ⟨X.obj.property, (boundedFlatPerfectSupportedOpenAcyclic_iff (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) X.obj).mp X.property⟩)
    (fun X ↦ ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ by
      have h := (supportedNativeAcyclic_evaluation_iff f T a X.obj).mp X.property
      unfold boundedFlatCoefficientSupportedEvaluation at h
      exact h)

private theorem supportedNativeAcyclicToFiber_evaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatPerfectSupportedWaldhausen
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).cof
      (boundedFlatPerfectSupportedWaldhausen
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedAcyclicToFiber f T a ⋙
        boundedFlatCoefficientSupportedEvaluation
        (boundedFlatCoefficientFiberSupportOpen f T a).ι) := by
  rw [supportedNativeAcyclicToFiber_evaluation]
  exact (supportedNativeAcyclicEvaluation_exact f T a).comp
    (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))

private theorem supportedEvaluation_reflects_exact {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] {C : Type*} [Category* C]
    (V : Structure C) (I : C ⥤ BoundedFlatCoefficientSupportedSections j)
    (h : IsExact V.cof V.weq (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (I ⋙ boundedFlatCoefficientSupportedEvaluation j)) :
    IsExact V.cof V.weq (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq I := by
  let := boundedFlatCoefficientSupportedEvaluation_isEquivalence j
  exact {
    zero := fun hZ ↦ IsZero.of_full_of_faithful_of_isZero
      (boundedFlatCoefficientSupportedEvaluation j) _ (h.zero hZ)
    cofibration := fun p hp ↦
      (boundedFlatCoefficientSupportedSectionWaldhausen_cof_iff j _).mpr (h.cofibration p hp)
    weak := fun p hp ↦
      (boundedFlatCoefficientSupportedSectionWaldhausen_weq_iff j _).mpr (h.weak p hp)
    pushout := fun hi hp ↦ IsPushout.of_map_of_faithful
      (boundedFlatCoefficientSupportedEvaluation j) (h.pushout hi hp) }

private theorem supportedNativeAcyclicToFiber_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.cof
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.weq
      (boundedFlatCoefficientSupportedAcyclicToFiber f T a) :=
  supportedEvaluation_reflects_exact (boundedFlatCoefficientFiberSupportOpen f T a).ι
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a))
    (boundedFlatCoefficientSupportedAcyclicToFiber f T a)
    (supportedNativeAcyclicToFiber_evaluation_exact f T a)

private def supportedNativeFiberAcyclicSmallEquivalence (a : Under R) :=
  (boundedFlatCoefficientSupportedFiberAcyclicEquivalence f T a).trans AsSmall.equiv.{u+1, u+1, 0}

private def supportedNativeFiberAcyclicModelMap (a : Under R) :
    boundedFlatCoefficientSupportedFiberModel f T a ⟶
      modelOf (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) where
  functor := (supportedNativeFiberAcyclicSmallEquivalence f T a).functor
  exact := (supportedNativeFiberToAcyclic_exact f T a).comp
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).smallModel_up_exact
  zero := rfl

private def supportedNativeAmbientModelMap (a : Under R) :
    boundedFlatCoefficientSupportedAmbientModel T a ⟶
      modelOf (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen where
  functor := AsSmall.up.{u+1, u+1, 0}
  exact := (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.smallModel_up_exact
  zero := rfl

private def supportedNativeCoarseModelMap (a : Under R) :
    boundedFlatCoefficientSupportedOpenModel f T a ⟶
      modelOf (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen where
  functor := AsSmall.up.{u+1, u+1, 0}
  exact := (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.smallModel_up_exact
  zero := rfl


private theorem supportedNativeEvaluation_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedFiberForgetModelMap f T a ≫
      supportedNativeAmbientModelMap T a =
    supportedNativeFiberAcyclicModelMap f T a ≫ modelMap _ _
      (acyclicInclusion_exact (boundedFlatCoefficientSupportedOpenNested f T a)) rfl := by
  apply Model.Hom.ext
  rfl

omit [IsOpenImmersion f.left] in
private theorem supportedNativeEvaluation_changeWeak (a : Under R) :
    boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a ≫
      supportedNativeCoarseModelMap f T a =
    supportedNativeAmbientModelMap T a ≫ modelMap _ _
      (changeWeak_exact (boundedFlatCoefficientSupportedOpenNested f T a))
      (boundedFlatCoefficientSupportedOpenNested f T a).zero_eq.symm := by
  apply Model.Hom.ext
  rfl

private def supportedNativeFiberEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap
        (boundedFlatCoefficientSupportedOpenNested f T a)) :=
  Arrow.homMk (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a))
    (prespectrumMap (supportedNativeAmbientModelMap T a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (supportedNativeEvaluation_inclusion f T a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

private theorem nativeAcyclicNull_square {C : Type u} [Category.{u} C]
    {V : Structure C} (N : NestedWeakEquivalences V) {W : Model.{u}}
    (F : W ⟶ (⟨Cat.of C, N.coarse⟩ : Model.{u}))
    (a : W ⟶ modelOf (acyclicStructure N))
    (c : (⟨Cat.of C, N.coarse⟩ : Model.{u}) ⟶ modelOf N.coarse)
    (hs : F ≫ c = a ≫ modelMap (acyclicStructure N) N.coarse
      (acyclicInclusion_coarse_exact N)
      (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm))
    (η : (Quillen.Waldhausen.IteratedS.zeroHom W
      (⟨Cat.of C, N.coarse⟩ : Model.{u})).functor ⟶ F.functor)
    (hη : ∀ X, N.coarse.weq (η.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum W).space n) :
    (prespectrumMap c).map n
      ((prespectrumTransformationHomotopy η hη).level n (unitInterval.symm s, x)) =
      (acyclicPrespectrumNullhomotopy N).level n
        (s, (prespectrumMap a).map n x) := by
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let θ : (Quillen.Waldhausen.IteratedS.zeroHom
      (modelOf (acyclicStructure N)) (modelOf N.coarse)).functor ⟶ G.functor :=
    whiskerLeft AsSmall.down.{u, u, 0}
      (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up.{u, u, 0})
  have hθ : ∀ A, (modelOf N.coarse).waldhausen.weq (θ.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.{u, u, 0}.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G a c hs η θ hη hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

private theorem supportedNativeFiberNull_evaluation (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    (prespectrumMap (supportedNativeCoarseModelMap f T a)).map n
      (((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n (s, x)) =
    (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a)).level n
      (s, (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a)).map n x) := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  let F := boundedFlatCoefficientSupportedFiberForgetModelMap f T a ≫
    boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ supportedNativeCoarseModelMap f T a =
      supportedNativeFiberAcyclicModelMap f T a ≫ G := by
    apply Model.Hom.ext
    rfl
  exact nativeAcyclicNull_square N F (supportedNativeFiberAcyclicModelMap f T a)
    (supportedNativeCoarseModelMap f T a) hs
    (boundedFlatCoefficientSupportedFiberZeroToOpen f T a)
    (boundedFlatCoefficientSupportedFiberZeroToOpen_weak f T a) n s x

/-- The actual native supported fibration proves the same original intersection-support cone
stable in every integer degree, without comparing independently chosen geometric zeros. -/
theorem boundedFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedFiberOpenConeComparison f T).app a) := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  have he : mappingConeMap (supportedNativeFiberEvaluationSquare f T a) ≫
      canonicalConePrespectrumMap N =
    (boundedFlatCoefficientSupportedFiberOpenConeComparison f T).app a ≫
      prespectrumMap (supportedNativeCoarseModelMap f T a) :=
    mappingConeDesc_naturality (supportedNativeFiberEvaluationSquare f T a)
      ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
      (changeWeakPrespectrumMap N) (prespectrumMap (supportedNativeCoarseModelMap f T a))
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      (acyclicPrespectrumNullhomotopy N)
      ((prespectrumFunctor.map_comp _ _).symm.trans
        ((congrArg prespectrumFunctor.map (supportedNativeEvaluation_changeWeak f T a)).trans
          (prespectrumFunctor.map_comp _ _))).symm (supportedNativeFiberNull_evaluation f T a)
  have hs := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSupportedFiberModel f T a)
    (W := modelOf (acyclicStructure N)) (supportedNativeFiberAcyclicSmallEquivalence f T a)
    ((supportedNativeFiberToAcyclic_exact f T a).comp (acyclicStructure N).smallModel_up_exact)
    ((acyclicStructure N).smallModel_down_exact.comp (supportedNativeAcyclicToFiber_exact f T a))
    (supportedNativeFiberAcyclicModelMap f T a).zero
  have ha := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSupportedAmbientModel T a)
    (W := modelOf (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen) AsSmall.equiv
    (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.smallModel_up_exact
    (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.smallModel_down_exact
    (supportedNativeAmbientModelMap T a).zero
  have hc := (mappingConeMap_isStableEquivalence_of_excision
    (supportedNativeFiberEvaluationSquare f T a)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _)
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) hs ha).comp
    (supportedNative_canonicalCone_isStableEquivalence f T a)
  rw [he] at hc
  have ho := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSupportedOpenModel f T a)
    (W := modelOf (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen) AsSmall.equiv
    (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.smallModel_up_exact
    (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.smallModel_down_exact
    (supportedNativeCoarseModelMap f T a).zero
  intro d
  let : IsIso ((stableHomotopyFunctor d).map
      (prespectrumMap (supportedNativeCoarseModelMap f T a))) := ho d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

end Quillen.PerfectComplexes
