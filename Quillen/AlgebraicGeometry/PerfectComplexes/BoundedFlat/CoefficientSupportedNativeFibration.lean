/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberLocalizationModels

/-!
# The original native auxiliary-supported canonical fiber map

Actual supported evaluation transfers coarse two-out-of-three and extension.
The original supported section joint data retain their second endpoint, so the
canonical native fiber map is a weak equivalence with its prescribed null.
No comparison of independently selected geometric zeros is required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
open HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

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

/-- Original supported section joints retain the actual second endpoint under evaluation. -/
theorem boundedFlatCoefficientSupportedSectionJoint_secondEndpoint {i : Index R} {U : Scheme.{u}}
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
    (boundedFlatCoefficientSupportedSectionJoint_secondEndpoint
      (boundedFlatCoefficientSupportOpen Q T a).ι)

/-- The original native auxiliary-support canonical fiber map is a weak equivalence. -/
theorem boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
    (a : Under R) :
    IsWeakHomotopyEquivalence
      (canonicalFiberMap (boundedFlatCoefficientSupportedOpenNested f T a)) := by
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
  exact canonicalFiberMap_isWeakHomotopyEquivalence_general N he
    (supportedNativeJointData f T a) (supportedNativeJoint_secondEndpoint f T a)


end Quillen.PerfectComplexes
